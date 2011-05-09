/* ===== semantic.c ===== */
#include <string>
#include <iostream>
#include <map>
#include <list>
#include <vector>


using namespace std;

#include <stdio.h>
#include <stdlib.h>
#include "ptype.hh"
#include "symtab.hh"

#include "myASTnode.hh"

#include "semantic.hh"
#include "util.hh"

// feedback the main program with our error status
int TypeError = 0;


/// ---------- Error reporting routines --------------

void errornumparam(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": The number of parameters in the call do not match."<<endl;
}

void errorincompatibleparam(int l,int n) {
  TypeError = 1;
  cout<<"L. "<<l<<": Parameter "<<n<<" with incompatible types."<<endl;
}

void errorreferenceableparam(int l,int n) {
  TypeError = 1;
  cout<<"L. "<<l<<": Parameter "<<n<<" is expected to be referenceable but it is not."<<endl;
}

void errordeclaredident(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Identifier "<<s<<" already declared."<<endl;
}

void errornondeclaredident(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Identifier "<<s<<" is undeclared."<<endl;
}

void errornonreferenceableleft(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Left expression of assignment is not referenceable."<<endl;
}

void errorincompatibleassignment(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Assignment with incompatible types."<<endl;
}

void errorbooleanrequired(int l,string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Instruction "<<s<<" requires a boolean condition."<<endl;
}

void errorisnotprocedure(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Operator ( must be applied to a procedure in an instruction."<<endl;
}

void errorisnotfunction(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Operator ( must be applied to a function in an expression."<<endl;
}

void errorincompatibleoperator(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Operator "<<s<<" with incompatible types."<<endl;
}

void errorincompatiblereturn(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Return with incompatible type."<<endl;
}

void errorreadwriterequirebasic(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Basic type required in "<<s<<"."<<endl;
}

void errornonreferenceableexpression(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Referenceable expression required in "<<s<<"."<<endl;
}

void errornonfielddefined(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Field "<<s<<" is not defined in the struct."<<endl;
}

void errorfielddefined(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Field "<<s<<" already defined in the struct."<<endl;
}

/// ------------------------------------------------------------
/// Table to store information about program identifiers
symtab symboltable;

static void InsertintoST(int line,string kind,string id,ptype tp)
{
  infosym p;

  if (symboltable.find(id) && symboltable.jumped_scopes(id)==0) errordeclaredident(line,id);
  else {
    symboltable.createsymbol(id);
    symboltable[id].kind=kind;
    symboltable[id].tp=tp;
  }
}

/// ------------------------------------------------------------

bool isbasickind(string kind) {
  return kind=="int" || kind=="bool" || kind=="string";
}



void check_params(AST *a,ptype tp,int line,int numparam)
{
  int cont=0;
  AST* params=a;
  
  while(params)
	{
		params = params->right;
		cont++;
	}
	
	if (cont != numparam) errornumparam(line);
	else {
	  params=a;
    cont=1;
    tp=tp->down;
    while(params) {
      TypeCheck(params);
      if (tp->kind == "parref" && !params->ref) errorreferenceableparam(line, cont);
      if (params->tp->kind != "error" && tp->kind != "error" && !equivalent_types(tp->down, params->tp)) 
        errorincompatibleparam(line, cont);
        
      tp=tp->right;
      params=params->right;
      cont++;
    }
  }
}

void insert_params(AST *a)
{
  if (!a) return;
  TypeCheck(a->down->right);
  if (a->kind=="ref") InsertintoST(a->line,"idparref",a->down->text,a->down->right->tp);
  else if (a->kind=="val") InsertintoST(a->line,"idparval",a->down->text,a->down->right->tp);
  insert_params(a->right);
}

void insert_vars(AST *a)
{
  if (!a) return;
  TypeCheck(child(a,0));
  InsertintoST(a->line,"idvarlocal",a->text,child(a,0)->tp);
  insert_vars(a->right); 
}

void construct_struct(AST *a)
{
  AST *a1=child(a,0);
  a->tp=create_type("struct",0,0);

  while (a1!=0) {
    TypeCheck(child(a1,0));
    if (a->tp->struct_field.find(a1->text)==a->tp->struct_field.end()) {
      a->tp->struct_field[a1->text]=child(a1,0)->tp;
      a->tp->ids.push_back(a1->text);
     } else {
      errorfielddefined(a1->line,a1->text);
    }
    a1=a1->right;
  }
}

void create_header(AST *a)
{
  a->tp=create_type(a->kind,0,0);
  AST *params = child(child(child(a,0),0),0);
  
  int cont = 0;
  ptype actual, anterior;
  anterior = NULL;
  while(params!=0) {
    actual=create_type("par"+params->kind,0,0);

    if(anterior==NULL) a->tp->down=actual;
    else anterior->right=actual;
    
    TypeCheck(child(params,1));
    actual->down=child(params,1)->tp;
    anterior=actual;
   
    params=params->right;
    cont++;
  }
  a->tp->numelemsarray = cont;
  
  if(a->kind=="function") {
    TypeCheck(child(child(a,0),1));
    a->tp->right = child(child(a,0),1)->tp;
  }
}


void insert_header(AST *a)
{
  create_header(a);
  if (a->kind=="function") InsertintoST(a->line,"idfunc",child(a,0)->text,a->tp);	
  if (a->kind=="procedure") InsertintoST(a->line,"idprocedure",child(a,0)->text,a->tp);
}

void insert_headers(AST *a)
{
  while (a!=0) {
    insert_header(a);
    a=a->right;
  }
}


void TypeCheck(AST *a,string info)
{
  if (!a) {
    return;
  }

  //cout<<"Starting with node \""<<a->kind<<"\""<<endl;
  if (a->kind=="program") {
    a->sc=symboltable.push();
    
    insert_vars(child(child(a,0),0));
    insert_headers(child(child(a,1),0));
    TypeCheck(child(a,1));
//    symboltable.write();
    TypeCheck(child(a,2),"instruction");

    symboltable.pop();
  }
  else if (a->kind=="procedure") {
    a->sc=symboltable.push();
    
    insert_params(child(child(child(a,0),0),0));
    insert_vars(child(child(a,1),0));
    insert_headers(child(child(a,2),0));
    TypeCheck(child(a,2));
    TypeCheck(child(a,3),"instruction");
    
    symboltable.pop();
  }
  else if (a->kind=="function") {
    a->sc=symboltable.push();
    
    insert_params(child(child(child(a,0),0),0));
    insert_vars(child(child(a,1),0));
    insert_headers(child(child(a,2),0));
    TypeCheck(child(a,2));
    TypeCheck(child(a,3),"instruction");
    TypeCheck(child(a,4));
    
    if(!equivalent_types(child(a,4)->tp,a->tp->right))
      errorincompatiblereturn(child(a,4)->line);
    
    symboltable.pop();
  }
  else if(a->kind=="val"||a->kind=="ref") {
    a->tp=create_type("par"+a->kind,0,0);
  }
  else if (a->kind=="list") {
    // At this point only instruction, procedures or parameters lists are possible.
    for (AST *a1=a->down;a1!=0;a1=a1->right) {
      TypeCheck(a1,info);
    }
  } 
  else if (a->kind=="ident") {
    if (!symboltable.find(a->text)) {
      errornondeclaredident(a->line, a->text);
    } 
    else {
      a->tp=symboltable[a->text].tp;
      if (a->tp->kind=="procedure" || a->tp->kind=="function") a->ref = 0;
      else a->ref=1;
    }
  } 
  else if (a->kind=="struct") {
    construct_struct(a);
  }
  else if (a->kind==":=") {
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
    
//    cout<<child(a,0)->tp->kind<<endl;
//    cout<<child(a,1)->tp->kind<<endl;
    
    if (!child(a,0)->ref) {
      errornonreferenceableleft(a->line,child(a,0)->text);
    }
    else if (child(a,0)->tp->kind!="error" && child(a,1)->tp->kind!="error" &&
	     !equivalent_types(child(a,0)->tp,child(a,1)->tp)) {
          errorincompatibleassignment(a->line);
    } 
    else {
      a->tp=child(a,0)->tp;
    }
  } 
  else if (a->kind=="intconst") {
    a->tp=create_type("int",0,0);
  } 
  else if (a->kind=="true" || a->kind=="false") {
    a->tp=create_type("bool",0,0);
  }
  else if (a->kind=="string") {
    a->tp=create_type("string",0,0);
  } 
  else if (a->kind=="+" || (a->kind=="-" && child(a,1)!=0) || a->kind=="*"
	   || a->kind=="/") {
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
    if ((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="int") ||
	(child(a,1)->tp->kind!="error" && child(a,1)->tp->kind!="int")) {
      errorincompatibleoperator(a->line,a->kind);
    }
    a->tp=create_type("int",0,0);
  }
  else if (isbasickind(a->kind)) {
    a->tp=create_type(a->kind,0,0);
  }
  else if (a->kind=="writeln") {
    TypeCheck(child(a,0));
    if (child(a,0)->tp->kind!="error" && !isbasickind(child(a,0)->tp->kind)) {
      errorreadwriterequirebasic(a->line,a->kind);
    }
  }
  else if (a->kind==".") {
    TypeCheck(child(a,0));
    a->ref=child(a,0)->ref;
    if (child(a,0)->tp->kind!="error") {
      if (child(a,0)->tp->kind!="struct") {
        errorincompatibleoperator(a->line,"struct.");
      }
      else if ((child(a,0)->tp->struct_field.find(child(a,1)->text)==child(a,0)->tp->struct_field.end())) {
          errornonfielddefined(a->line,child(a,1)->text);
      } 
      else {
      	a->tp=child(a,0)->tp->struct_field[child(a,1)->text];
      }
    }
  }
  else if (a->kind=="and" | a->kind=="or") {
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
    if ((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="bool") ||
        (child(a,1)->tp->kind!="error" && child(a,1)->tp->kind!="bool")) {
      errorincompatibleoperator(a->line,a->kind);
    }
    a->tp=create_type("bool",0,0);
  }
  else if (a->kind=="not") {
    TypeCheck(child(a,0));
    if ((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="bool")) {
      errorincompatibleoperator(a->line,a->kind);
    }
    a->tp=create_type("bool",0,0);
  }
  else if (a->kind=="-") {
    TypeCheck(child(a,0));
    if ((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="int")) {
      errorincompatibleoperator(a->line,a->kind);
    }
    a->tp=create_type("int",0,0);
  }
  else if (a->kind=="<" || a->kind==">") {
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
    if ((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="int") ||
        (child(a,1)->tp->kind!="error" && child(a,1)->tp->kind!="int")) {
      errorincompatibleoperator(a->line,a->kind);
    }
    a->tp=create_type("bool",0,0);
  }
  else if (a->kind=="=") {
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
    if(((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="int") ||
        (child(a,1)->tp->kind!="error" && child(a,1)->tp->kind!="int")) &&
       ((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="bool") ||
        (child(a,1)->tp->kind!="error" && child(a,1)->tp->kind!="bool"))) {
      errorincompatibleoperator(a->line,a->kind);
    }
    a->tp=create_type("bool",0,0);
  }
  else if (a->kind=="if") {
    TypeCheck(child(a,0));
    if ((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="bool")) {
      errorbooleanrequired(a->line,a->kind);
    }
    TypeCheck(child(a,1),"instruction");
    if(child(a,2)!=0) TypeCheck(child(a,2),"instruction");
  }
  else if (a->kind=="while") {
    TypeCheck(child(a,0));
    if ((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="bool")) {
      errorbooleanrequired(a->line,a->kind);
    }
    TypeCheck(child(a,1),"instruction");
  }
  else if (a->kind=="array") {
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
    //cout<<child(a,1)->tp->kind<<endl;
    if ((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="int") ||
        (child(a,1)->tp->kind!="error" && child(a,1)->tp->kind!="bool" &&
         child(a,1)->tp->kind!="struct" &&
         child(a,1)->tp->kind!="int" &&
         child(a,1)->tp->kind!="array")) {
      errorincompatibleoperator(a->line,a->kind);
    }
    a->tp=create_type("array",child(a,1)->tp,0);
    a->tp->numelemsarray=stringtoint(child(a,0)->text);
  }
  else if (a->kind=="[") {
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
    if (child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="array") {
        errorincompatibleoperator(a->line,"array[]");
    }
    if (child(a,1)->tp->kind!="error" && child(a,1)->tp->kind!="int") {
      errorincompatibleoperator(a->line,"[]");
    }
    
    if(child(a,0)->tp->kind=="array") {
      a->tp=child(a,0)->tp->down;
    }
    a->ref=child(a,0)->ref;
  }
  else if (a->kind=="(") {
    if (!symboltable.find(child(a,0)->text)) {
      errornondeclaredident(a->line,child(a,0)->text);
    } else if(info=="instruction") {
      a->tp = symboltable[child(a,0)->text].tp;
      if(a->tp->kind=="procedure") {
        check_params(child(child(a,1),0),a->tp,a->line,a->tp->numelemsarray);
      } else {
        errorisnotprocedure(a->line);
        if(a->tp->kind=="function") {
          check_params(child(child(a,1),0),a->tp,a->line,a->tp->numelemsarray);
        }
      }
    } else {
      a->tp = symboltable[child(a,0)->text].tp;
      if(a->tp->kind=="function") {
        check_params(child(child(a,1),0),a->tp,a->line,a->tp->numelemsarray);
        a->tp=a->tp->right;
      } else {
        errorisnotfunction(a->line);
        if(a->tp->kind=="procedure") {
          check_params(child(child(a,1),0),a->tp,a->line,a->tp->numelemsarray);
          a->tp=create_type("error",0,0);
        }
      }
    }
  }
  else if (a->kind=="read") {
    TypeCheck(child(a,0));
		if (child(a,0)->tp->kind!="error")
		{
			if (child(a,0)->ref==0)
			  errornonreferenceableexpression(a->line,a->kind);
			else if (!isbasickind(child(a,0)->tp->kind))
			  errorreadwriterequirebasic(a->line,a->kind); 
		}
  }
  else if (a->kind=="write") {
    TypeCheck(child(a,0));
		if (child(a,0)->tp->kind!="error")
		{
			if (!isbasickind(child(a,0)->tp->kind))
			  errorreadwriterequirebasic(a->line,a->kind); 
		}
  }
  else {
    cout<<"BIG PROBLEM! No case defined for kind "<<a->kind<<endl;
  }

  //cout<<"Ending with node \""<<a->kind<<"\""<<endl;
}
