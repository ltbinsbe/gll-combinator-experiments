module GLLCombParser (GLLCombParser.parse,Abstract_declarator,Additive_expression,And_expression,Argument_expression_list,Assignment_expression,Assignment_operator,Cast_expression,Character_constant,Compound_statement,Conditional_expression,Constant,Constant_expression,Declaration,Declaration_list,Declaration_specifiers,Declarator,Direct_abstract_declarator,Direct_declarator,Enum_specifier,Enumeration_constant,Enumerator,Enumerator_list,Equality_expression,Exclusive_or_expression,Expression,Expression_statement,External_declaration,Floating_constant,Function_definition,Identifier,Identifier_list,Inclusive_or_expression,Init_declarator,Init_declarator_list,Initializer,Initializer_list,Integer_constant,Iteration_statement,Jump_statement,Labeled_statement,Logical_and_expression,Logical_or_expression,Multiplicative_expression,Parameter_declaration,Parameter_list,Parameter_type_list,Pointer,Postfix_expression,Primary_expression,Relational_expression,Selection_statement,Shift_expression,Specifier_qualifier_list,Statement,Statement_list,Storage_class_specifier,Stringlit,Struct_declaration,Struct_declaration_list,Struct_declarator,Struct_declarator_list,Struct_or_union,Struct_or_union_specifier,Translation_unit,Type_name,Type_qualifier,Type_qualifier_list,Type_specifier,Typedef_name,Unary_expression,Unary_operator,GLLCombParser.Token(..)) where
--import GLL.Combinators.BinaryInterface as Lib
--import GLL.Combinators.Interface as Lib
--import GLL.ParserCombinators as Lib
import GLL.ParserCombinatorsLookahead as Lib
data Abstract_declarator = Abstract_declarator1 Pointer
                         | Abstract_declarator2 Pointer Direct_abstract_declarator
                         | Abstract_declarator3 Direct_abstract_declarator
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Additive_expression = Additive_expression1 Multiplicative_expression
                         | Additive_expression2 Additive_expression Multiplicative_expression
                         | Additive_expression3 Additive_expression Multiplicative_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data And_expression = And_expression1 Equality_expression
                    | And_expression2 And_expression Equality_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Argument_expression_list = Argument_expression_list1 Assignment_expression
                              | Argument_expression_list2 Argument_expression_list Assignment_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Assignment_expression = Assignment_expression1 Conditional_expression
                           | Assignment_expression2 Unary_expression Assignment_operator Assignment_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Assignment_operator = Assignment_operator1
                         | Assignment_operator10
                         | Assignment_operator11
                         | Assignment_operator2
                         | Assignment_operator3
                         | Assignment_operator4
                         | Assignment_operator5
                         | Assignment_operator6
                         | Assignment_operator7
                         | Assignment_operator8
                         | Assignment_operator9
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Cast_expression = Cast_expression1 Unary_expression
                     | Cast_expression2 Type_name Cast_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Character_constant = Character_constant1
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Compound_statement = Compound_statement1 Declaration_list Statement_list
                        | Compound_statement2 Statement_list
                        | Compound_statement3 Declaration_list
                        | Compound_statement4
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Conditional_expression = Conditional_expression1 Logical_or_expression
                            | Conditional_expression2 Logical_or_expression Expression Conditional_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Constant = Constant1 Integer_constant
              | Constant2 Floating_constant
              | Constant3 Enumeration_constant
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Constant_expression = Constant_expression1 Conditional_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Declaration = Declaration1 Declaration_specifiers Init_declarator_list
                 | Declaration2 Declaration_specifiers
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Declaration_list = Declaration_list1 Declaration
                      | Declaration_list2 Declaration_list Declaration
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Declaration_specifiers = Declaration_specifiers1 Storage_class_specifier Declaration_specifiers
                            | Declaration_specifiers2 Storage_class_specifier
                            | Declaration_specifiers3 Type_specifier Declaration_specifiers
                            | Declaration_specifiers4 Type_specifier
                            | Declaration_specifiers5 Type_qualifier Declaration_specifiers
                            | Declaration_specifiers6 Type_qualifier
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Declarator = Declarator1 Pointer Direct_declarator
                | Declarator2 Direct_declarator
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Direct_abstract_declarator = Direct_abstract_declarator1 Abstract_declarator
                                | Direct_abstract_declarator2 Direct_abstract_declarator Constant_expression
                                | Direct_abstract_declarator3 Constant_expression
                                | Direct_abstract_declarator4 Direct_abstract_declarator
                                | Direct_abstract_declarator5
                                | Direct_abstract_declarator6 Direct_abstract_declarator Parameter_type_list
                                | Direct_abstract_declarator7 Parameter_type_list
                                | Direct_abstract_declarator8 Direct_abstract_declarator
                                | Direct_abstract_declarator9
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Direct_declarator = Direct_declarator1 Identifier
                       | Direct_declarator2 Declarator
                       | Direct_declarator3 Direct_declarator Constant_expression
                       | Direct_declarator4 Direct_declarator
                       | Direct_declarator5 Direct_declarator Parameter_type_list
                       | Direct_declarator6 Direct_declarator Identifier_list
                       | Direct_declarator7 Direct_declarator
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Enum_specifier = Enum_specifier1 Identifier Enumerator_list
                    | Enum_specifier2 Enumerator_list
                    | Enum_specifier3 Identifier
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Enumeration_constant = Enumeration_constant1
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Enumerator = Enumerator1 Identifier
                | Enumerator2 Identifier Constant_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Enumerator_list = Enumerator_list1 Enumerator
                     | Enumerator_list2 Enumerator_list Enumerator
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Equality_expression = Equality_expression1 Relational_expression
                         | Equality_expression2 Equality_expression Relational_expression
                         | Equality_expression3 Equality_expression Relational_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Exclusive_or_expression = Exclusive_or_expression1 And_expression
                             | Exclusive_or_expression2 Exclusive_or_expression And_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Expression = Expression1 Assignment_expression
                | Expression2 Expression Assignment_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Expression_statement = Expression_statement1 Expression
                          | Expression_statement2
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data External_declaration = External_declaration1 Function_definition
                          | External_declaration2 Declaration
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Floating_constant = Floating_constant1
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Function_definition = Function_definition1 Declaration_specifiers Declarator Declaration_list Compound_statement
                         | Function_definition2 Declarator Declaration_list Compound_statement
                         | Function_definition3 Declaration_specifiers Declarator Compound_statement
                         | Function_definition4 Declarator Compound_statement
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Identifier = Identifier1
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Identifier_list = Identifier_list1 Identifier
                     | Identifier_list2 Identifier_list Identifier
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Inclusive_or_expression = Inclusive_or_expression1 Exclusive_or_expression
                             | Inclusive_or_expression2 Inclusive_or_expression Exclusive_or_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Init_declarator = Init_declarator1 Declarator
                     | Init_declarator2 Declarator Initializer
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Init_declarator_list = Init_declarator_list1 Init_declarator
                          | Init_declarator_list2 Init_declarator_list Init_declarator
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Initializer = Initializer1 Assignment_expression
                 | Initializer2 Initializer_list
                 | Initializer3 Initializer_list
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Initializer_list = Initializer_list1 Initializer
                      | Initializer_list2 Initializer_list Initializer
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Integer_constant = Integer_constant1
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Iteration_statement = Iteration_statement1 Expression Statement
                         | Iteration_statement10 Statement
                         | Iteration_statement2 Statement Expression
                         | Iteration_statement3 Expression Expression Expression Statement
                         | Iteration_statement4 Expression Expression Statement
                         | Iteration_statement5 Expression Expression Statement
                         | Iteration_statement6 Expression Statement
                         | Iteration_statement7 Expression Expression Statement
                         | Iteration_statement8 Expression Statement
                         | Iteration_statement9 Expression Statement
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Jump_statement = Jump_statement1 Identifier
                    | Jump_statement2
                    | Jump_statement3
                    | Jump_statement4 Expression
                    | Jump_statement5
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Labeled_statement = Labeled_statement1 Identifier Statement
                       | Labeled_statement2 Constant_expression Statement
                       | Labeled_statement3 Statement
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Logical_and_expression = Logical_and_expression1 Inclusive_or_expression
                            | Logical_and_expression2 Logical_and_expression Inclusive_or_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Logical_or_expression = Logical_or_expression1 Logical_and_expression
                           | Logical_or_expression2 Logical_or_expression Logical_and_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Multiplicative_expression = Multiplicative_expression1 Cast_expression
                               | Multiplicative_expression2 Multiplicative_expression Cast_expression
                               | Multiplicative_expression3 Multiplicative_expression Cast_expression
                               | Multiplicative_expression4 Multiplicative_expression Cast_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Parameter_declaration = Parameter_declaration1 Declaration_specifiers Declarator
                           | Parameter_declaration2 Declaration_specifiers Abstract_declarator
                           | Parameter_declaration3 Declaration_specifiers
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Parameter_list = Parameter_list1 Parameter_declaration
                    | Parameter_list2 Parameter_list Parameter_declaration
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Parameter_type_list = Parameter_type_list1 Parameter_list
                         | Parameter_type_list2 Parameter_list
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Pointer = Pointer1 Type_qualifier_list
             | Pointer2
             | Pointer3 Type_qualifier_list Pointer
             | Pointer4 Pointer
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Postfix_expression = Postfix_expression1 Primary_expression
                        | Postfix_expression2 Postfix_expression Expression
                        | Postfix_expression3 Postfix_expression Argument_expression_list
                        | Postfix_expression4 Postfix_expression
                        | Postfix_expression5 Postfix_expression Identifier
                        | Postfix_expression6 Postfix_expression Identifier
                        | Postfix_expression7 Postfix_expression
                        | Postfix_expression8 Postfix_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Primary_expression = Primary_expression1 Identifier
                        | Primary_expression2 Constant
                        | Primary_expression3 Stringlit
                        | Primary_expression4 Expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Relational_expression = Relational_expression1 Shift_expression
                           | Relational_expression2 Relational_expression Shift_expression
                           | Relational_expression3 Relational_expression Shift_expression
                           | Relational_expression4 Relational_expression Shift_expression
                           | Relational_expression5 Relational_expression Shift_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Selection_statement = Selection_statement1 Expression Statement
                         | Selection_statement2 Expression Statement Statement
                         | Selection_statement3 Expression Statement
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Shift_expression = Shift_expression1 Additive_expression
                      | Shift_expression2 Shift_expression Additive_expression
                      | Shift_expression3 Shift_expression Additive_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Specifier_qualifier_list = Specifier_qualifier_list1 Type_specifier Specifier_qualifier_list
                              | Specifier_qualifier_list2 Type_specifier
                              | Specifier_qualifier_list3 Type_qualifier Specifier_qualifier_list
                              | Specifier_qualifier_list4 Type_qualifier
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Statement = Statement1 Labeled_statement
               | Statement2 Expression_statement
               | Statement3 Compound_statement
               | Statement4 Selection_statement
               | Statement5 Iteration_statement
               | Statement6 Jump_statement
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Statement_list = Statement_list1 Statement
                    | Statement_list2 Statement_list Statement
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Storage_class_specifier = Storage_class_specifier1
                             | Storage_class_specifier2
                             | Storage_class_specifier3
                             | Storage_class_specifier4
                             | Storage_class_specifier5
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Stringlit = Stringlit1
               | Stringlit2 Stringlit
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Struct_declaration = Struct_declaration1 Specifier_qualifier_list Struct_declarator_list
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Struct_declaration_list = Struct_declaration_list1 Struct_declaration
                             | Struct_declaration_list2 Struct_declaration_list Struct_declaration
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Struct_declarator = Struct_declarator1 Declarator
                       | Struct_declarator2 Declarator Constant_expression
                       | Struct_declarator3 Constant_expression
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Struct_declarator_list = Struct_declarator_list1 Struct_declarator
                            | Struct_declarator_list2 Struct_declarator_list Struct_declarator
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Struct_or_union = Struct_or_union1
                     | Struct_or_union2
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Struct_or_union_specifier = Struct_or_union_specifier1 Struct_or_union Identifier Struct_declaration_list
                               | Struct_or_union_specifier2 Struct_or_union Struct_declaration_list
                               | Struct_or_union_specifier3 Struct_or_union Identifier
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Translation_unit = Translation_unit1 External_declaration
                      | Translation_unit2 Translation_unit External_declaration
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Type_name = Type_name1 Specifier_qualifier_list Abstract_declarator
               | Type_name2 Specifier_qualifier_list
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Type_qualifier = Type_qualifier1
                    | Type_qualifier2
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Type_qualifier_list = Type_qualifier_list1 Type_qualifier
                         | Type_qualifier_list2 Type_qualifier_list Type_qualifier
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Type_specifier = Type_specifier1
                    | Type_specifier10 Struct_or_union_specifier
                    | Type_specifier11 Enum_specifier
                    | Type_specifier12 Typedef_name
                    | Type_specifier2
                    | Type_specifier3
                    | Type_specifier4
                    | Type_specifier5
                    | Type_specifier6
                    | Type_specifier7
                    | Type_specifier8
                    | Type_specifier9
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Typedef_name = Typedef_name1
                  | Typedef_name2
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Unary_expression = Unary_expression1 Postfix_expression
                      | Unary_expression2 Unary_expression
                      | Unary_expression3 Unary_expression
                      | Unary_expression4 Unary_operator Cast_expression
                      | Unary_expression5 Unary_expression
                      | Unary_expression6 Type_name
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
data Unary_operator = Unary_operator1
                    | Unary_operator2
                    | Unary_operator3
                    | Unary_operator4
                    | Unary_operator5
                    | Unary_operator6
  deriving (Prelude.Show,Prelude.Eq,Prelude.Ord)
p_Abstract_declarator = "Abstract_declarator" <:=> Abstract_declarator1 <$$> p_Pointer<||>
                                                 Abstract_declarator2 <$$> p_Pointer <**> p_Direct_abstract_declarator<||>
                                                 Abstract_declarator3 <$$> p_Direct_abstract_declarator
p_Additive_expression = "Additive_expression" <:=> Additive_expression1 <$$> p_Multiplicative_expression<||>
                                                 Additive_expression2 <$$> p_Additive_expression <** term (GLLCombParser.Token "+" Nothing) <**> p_Multiplicative_expression<||>
                                                 Additive_expression3 <$$> p_Additive_expression <** term (GLLCombParser.Token "-" Nothing) <**> p_Multiplicative_expression
p_And_expression = "And_expression" <:=> And_expression1 <$$> p_Equality_expression<||>
                                       And_expression2 <$$> p_And_expression <** term (GLLCombParser.Token "&" Nothing) <**> p_Equality_expression
p_Argument_expression_list = "Argument_expression_list" <:=> Argument_expression_list1 <$$> p_Assignment_expression<||>
                                                           Argument_expression_list2 <$$> p_Argument_expression_list <** term (GLLCombParser.Token "," Nothing) <**> p_Assignment_expression
p_Assignment_expression = "Assignment_expression" <:=> Assignment_expression1 <$$> p_Conditional_expression<||>
                                                     Assignment_expression2 <$$> p_Unary_expression <**> p_Assignment_operator <**> p_Assignment_expression
p_Assignment_operator = "Assignment_operator" <:=> Assignment_operator1 <$$ term (GLLCombParser.Token "=" Nothing)<||>
                                                 Assignment_operator10 <$$ term (GLLCombParser.Token "^=" Nothing)<||>
                                                 Assignment_operator11 <$$ term (GLLCombParser.Token "|=" Nothing)<||>
                                                 Assignment_operator2 <$$ term (GLLCombParser.Token "*=" Nothing)<||>
                                                 Assignment_operator3 <$$ term (GLLCombParser.Token "/=" Nothing)<||>
                                                 Assignment_operator4 <$$ term (GLLCombParser.Token "%=" Nothing)<||>
                                                 Assignment_operator5 <$$ term (GLLCombParser.Token "+=" Nothing)<||>
                                                 Assignment_operator6 <$$ term (GLLCombParser.Token "-=" Nothing)<||>
                                                 Assignment_operator7 <$$ term (GLLCombParser.Token "<<=" Nothing)<||>
                                                 Assignment_operator8 <$$ term (GLLCombParser.Token ">>=" Nothing)<||>
                                                 Assignment_operator9 <$$ term (GLLCombParser.Token "&=" Nothing)
p_Cast_expression = "Cast_expression" <:=> Cast_expression1 <$$> p_Unary_expression<||>
                                         Cast_expression2 <$$ term (GLLCombParser.Token "(" Nothing) <**> p_Type_name <** term (GLLCombParser.Token ")" Nothing) <**> p_Cast_expression
p_Character_constant = "Character_constant" <:=> Character_constant1 <$$ term (GLLCombParser.Token "STRING" Nothing)
p_Compound_statement = "Compound_statement" <:=> Compound_statement1 <$$ term (GLLCombParser.Token "{" Nothing) <**> p_Declaration_list <**> p_Statement_list <** term (GLLCombParser.Token "}" Nothing)<||>
                                               Compound_statement2 <$$ term (GLLCombParser.Token "{" Nothing) <**> p_Statement_list <** term (GLLCombParser.Token "}" Nothing)<||>
                                               Compound_statement3 <$$ term (GLLCombParser.Token "{" Nothing) <**> p_Declaration_list <** term (GLLCombParser.Token "}" Nothing)<||>
                                               Compound_statement4 <$$ term (GLLCombParser.Token "{" Nothing) <** term (GLLCombParser.Token "}" Nothing)
p_Conditional_expression = "Conditional_expression" <:=> Conditional_expression1 <$$> p_Logical_or_expression<||>
                                                       Conditional_expression2 <$$> p_Logical_or_expression <** term (GLLCombParser.Token "?" Nothing) <**> p_Expression <** term (GLLCombParser.Token ":" Nothing) <**> p_Conditional_expression
p_Constant = "Constant" <:=> Constant1 <$$> p_Integer_constant<||>
                           Constant2 <$$> p_Floating_constant<||>
                           Constant3 <$$> p_Enumeration_constant
p_Constant_expression = "Constant_expression" <:=> Constant_expression1 <$$> p_Conditional_expression
p_Declaration = "Declaration" <:=> Declaration1 <$$> p_Declaration_specifiers <**> p_Init_declarator_list <** term (GLLCombParser.Token ";" Nothing)<||>
                                 Declaration2 <$$> p_Declaration_specifiers <** term (GLLCombParser.Token ";" Nothing)
p_Declaration_list = "Declaration_list" <:=> Declaration_list1 <$$> p_Declaration<||>
                                           Declaration_list2 <$$> p_Declaration_list <**> p_Declaration
p_Declaration_specifiers = "Declaration_specifiers" <:=> Declaration_specifiers1 <$$> p_Storage_class_specifier <**> p_Declaration_specifiers<||>
                                                       Declaration_specifiers2 <$$> p_Storage_class_specifier<||>
                                                       Declaration_specifiers3 <$$> p_Type_specifier <**> p_Declaration_specifiers<||>
                                                       Declaration_specifiers4 <$$> p_Type_specifier<||>
                                                       Declaration_specifiers5 <$$> p_Type_qualifier <**> p_Declaration_specifiers<||>
                                                       Declaration_specifiers6 <$$> p_Type_qualifier
p_Declarator = "Declarator" <:=> Declarator1 <$$> p_Pointer <**> p_Direct_declarator<||>
                               Declarator2 <$$> p_Direct_declarator
p_Direct_abstract_declarator = "Direct_abstract_declarator" <:=> Direct_abstract_declarator1 <$$ term (GLLCombParser.Token "(" Nothing) <**> p_Abstract_declarator <** term (GLLCombParser.Token ")" Nothing)<||>
                                                               Direct_abstract_declarator2 <$$> p_Direct_abstract_declarator <** term (GLLCombParser.Token "[" Nothing) <**> p_Constant_expression <** term (GLLCombParser.Token "]" Nothing)<||>
                                                               Direct_abstract_declarator3 <$$ term (GLLCombParser.Token "[" Nothing) <**> p_Constant_expression <** term (GLLCombParser.Token "]" Nothing)<||>
                                                               Direct_abstract_declarator4 <$$> p_Direct_abstract_declarator <** term (GLLCombParser.Token "[" Nothing) <** term (GLLCombParser.Token "]" Nothing)<||>
                                                               Direct_abstract_declarator5 <$$ term (GLLCombParser.Token "[" Nothing) <** term (GLLCombParser.Token "]" Nothing)<||>
                                                               Direct_abstract_declarator6 <$$> p_Direct_abstract_declarator <** term (GLLCombParser.Token "(" Nothing) <**> p_Parameter_type_list <** term (GLLCombParser.Token ")" Nothing)<||>
                                                               Direct_abstract_declarator7 <$$ term (GLLCombParser.Token "(" Nothing) <**> p_Parameter_type_list <** term (GLLCombParser.Token ")" Nothing)<||>
                                                               Direct_abstract_declarator8 <$$> p_Direct_abstract_declarator <** term (GLLCombParser.Token "(" Nothing) <** term (GLLCombParser.Token ")" Nothing)<||>
                                                               Direct_abstract_declarator9 <$$ term (GLLCombParser.Token "(" Nothing) <** term (GLLCombParser.Token ")" Nothing)
p_Direct_declarator = "Direct_declarator" <:=> Direct_declarator1 <$$> p_Identifier<||>
                                             Direct_declarator2 <$$ term (GLLCombParser.Token "(" Nothing) <**> p_Declarator <** term (GLLCombParser.Token ")" Nothing)<||>
                                             Direct_declarator3 <$$> p_Direct_declarator <** term (GLLCombParser.Token "[" Nothing) <**> p_Constant_expression <** term (GLLCombParser.Token "]" Nothing)<||>
                                             Direct_declarator4 <$$> p_Direct_declarator <** term (GLLCombParser.Token "[" Nothing) <** term (GLLCombParser.Token "]" Nothing)<||>
                                             Direct_declarator5 <$$> p_Direct_declarator <** term (GLLCombParser.Token "(" Nothing) <**> p_Parameter_type_list <** term (GLLCombParser.Token ")" Nothing)<||>
                                             Direct_declarator6 <$$> p_Direct_declarator <** term (GLLCombParser.Token "(" Nothing) <**> p_Identifier_list <** term (GLLCombParser.Token ")" Nothing)<||>
                                             Direct_declarator7 <$$> p_Direct_declarator <** term (GLLCombParser.Token "(" Nothing) <** term (GLLCombParser.Token ")" Nothing)
p_Enum_specifier = "Enum_specifier" <:=> Enum_specifier1 <$$ term (GLLCombParser.Token "enum" Nothing) <**> p_Identifier <** term (GLLCombParser.Token "{" Nothing) <**> p_Enumerator_list <** term (GLLCombParser.Token "}" Nothing)<||>
                                       Enum_specifier2 <$$ term (GLLCombParser.Token "enum" Nothing) <** term (GLLCombParser.Token "{" Nothing) <**> p_Enumerator_list <** term (GLLCombParser.Token "}" Nothing)<||>
                                       Enum_specifier3 <$$ term (GLLCombParser.Token "enum" Nothing) <**> p_Identifier
p_Enumeration_constant = "Enumeration_constant" <:=> Enumeration_constant1 <$$ term (GLLCombParser.Token "ENUM_ID" Nothing)
p_Enumerator = "Enumerator" <:=> Enumerator1 <$$> p_Identifier<||>
                               Enumerator2 <$$> p_Identifier <** term (GLLCombParser.Token "=" Nothing) <**> p_Constant_expression
p_Enumerator_list = "Enumerator_list" <:=> Enumerator_list1 <$$> p_Enumerator<||>
                                         Enumerator_list2 <$$> p_Enumerator_list <** term (GLLCombParser.Token "," Nothing) <**> p_Enumerator
p_Equality_expression = "Equality_expression" <:=> Equality_expression1 <$$> p_Relational_expression<||>
                                                 Equality_expression2 <$$> p_Equality_expression <** term (GLLCombParser.Token "==" Nothing) <**> p_Relational_expression<||>
                                                 Equality_expression3 <$$> p_Equality_expression <** term (GLLCombParser.Token "!=" Nothing) <**> p_Relational_expression
p_Exclusive_or_expression = "Exclusive_or_expression" <:=> Exclusive_or_expression1 <$$> p_And_expression<||>
                                                         Exclusive_or_expression2 <$$> p_Exclusive_or_expression <** term (GLLCombParser.Token "^" Nothing) <**> p_And_expression
p_Expression = "Expression" <:=> Expression1 <$$> p_Assignment_expression<||>
                               Expression2 <$$> p_Expression <** term (GLLCombParser.Token "," Nothing) <**> p_Assignment_expression
p_Expression_statement = "Expression_statement" <:=> Expression_statement1 <$$> p_Expression <** term (GLLCombParser.Token ";" Nothing)<||>
                                                   Expression_statement2 <$$ term (GLLCombParser.Token ";" Nothing)
p_External_declaration = "External_declaration" <:=> External_declaration1 <$$> p_Function_definition<||>
                                                   External_declaration2 <$$> p_Declaration
p_Floating_constant = "Floating_constant" <:=> Floating_constant1 <$$ term (GLLCombParser.Token "REAL" Nothing)
p_Function_definition = "Function_definition" <:=> Function_definition1 <$$> p_Declaration_specifiers <**> p_Declarator <**> p_Declaration_list <**> p_Compound_statement<||>
                                                 Function_definition2 <$$> p_Declarator <**> p_Declaration_list <**> p_Compound_statement<||>
                                                 Function_definition3 <$$> p_Declaration_specifiers <**> p_Declarator <**> p_Compound_statement<||>
                                                 Function_definition4 <$$> p_Declarator <**> p_Compound_statement
p_Identifier = "Identifier" <:=> Identifier1 <$$ term (GLLCombParser.Token "ID" Nothing)
p_Identifier_list = "Identifier_list" <:=> Identifier_list1 <$$> p_Identifier<||>
                                         Identifier_list2 <$$> p_Identifier_list <** term (GLLCombParser.Token "," Nothing) <**> p_Identifier
p_Inclusive_or_expression = "Inclusive_or_expression" <:=> Inclusive_or_expression1 <$$> p_Exclusive_or_expression<||>
                                                         Inclusive_or_expression2 <$$> p_Inclusive_or_expression <** term (GLLCombParser.Token "|" Nothing) <**> p_Exclusive_or_expression
p_Init_declarator = "Init_declarator" <:=> Init_declarator1 <$$> p_Declarator<||>
                                         Init_declarator2 <$$> p_Declarator <** term (GLLCombParser.Token "=" Nothing) <**> p_Initializer
p_Init_declarator_list = "Init_declarator_list" <:=> Init_declarator_list1 <$$> p_Init_declarator<||>
                                                   Init_declarator_list2 <$$> p_Init_declarator_list <** term (GLLCombParser.Token "," Nothing) <**> p_Init_declarator
p_Initializer = "Initializer" <:=> Initializer1 <$$> p_Assignment_expression<||>
                                 Initializer2 <$$ term (GLLCombParser.Token "{" Nothing) <**> p_Initializer_list <** term (GLLCombParser.Token "}" Nothing)<||>
                                 Initializer3 <$$ term (GLLCombParser.Token "{" Nothing) <**> p_Initializer_list <** term (GLLCombParser.Token "," Nothing) <** term (GLLCombParser.Token "}" Nothing)
p_Initializer_list = "Initializer_list" <:=> Initializer_list1 <$$> p_Initializer<||>
                                           Initializer_list2 <$$> p_Initializer_list <** term (GLLCombParser.Token "," Nothing) <**> p_Initializer
p_Integer_constant = "Integer_constant" <:=> Integer_constant1 <$$ term (GLLCombParser.Token "INTEGER" Nothing)
p_Iteration_statement = "Iteration_statement" <:=> Iteration_statement1 <$$ term (GLLCombParser.Token "while" Nothing) <** term (GLLCombParser.Token "(" Nothing) <**> p_Expression <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement<||>
                                                 Iteration_statement10 <$$ term (GLLCombParser.Token "for" Nothing) <** term (GLLCombParser.Token "(" Nothing) <** term (GLLCombParser.Token ";" Nothing) <** term (GLLCombParser.Token ";" Nothing) <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement<||>
                                                 Iteration_statement2 <$$ term (GLLCombParser.Token "do" Nothing) <**> p_Statement <** term (GLLCombParser.Token "while" Nothing) <** term (GLLCombParser.Token "(" Nothing) <**> p_Expression <** term (GLLCombParser.Token ")" Nothing)<||>
                                                 Iteration_statement3 <$$ term (GLLCombParser.Token "for" Nothing) <** term (GLLCombParser.Token "(" Nothing) <**> p_Expression <** term (GLLCombParser.Token ";" Nothing) <**> p_Expression <** term (GLLCombParser.Token ";" Nothing) <**> p_Expression <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement<||>
                                                 Iteration_statement4 <$$ term (GLLCombParser.Token "for" Nothing) <** term (GLLCombParser.Token "(" Nothing) <**> p_Expression <** term (GLLCombParser.Token ";" Nothing) <**> p_Expression <** term (GLLCombParser.Token ";" Nothing) <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement<||>
                                                 Iteration_statement5 <$$ term (GLLCombParser.Token "for" Nothing) <** term (GLLCombParser.Token "(" Nothing) <**> p_Expression <** term (GLLCombParser.Token ";" Nothing) <** term (GLLCombParser.Token ";" Nothing) <**> p_Expression <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement<||>
                                                 Iteration_statement6 <$$ term (GLLCombParser.Token "for" Nothing) <** term (GLLCombParser.Token "(" Nothing) <**> p_Expression <** term (GLLCombParser.Token ";" Nothing) <** term (GLLCombParser.Token ";" Nothing) <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement<||>
                                                 Iteration_statement7 <$$ term (GLLCombParser.Token "for" Nothing) <** term (GLLCombParser.Token "(" Nothing) <** term (GLLCombParser.Token ";" Nothing) <**> p_Expression <** term (GLLCombParser.Token ";" Nothing) <**> p_Expression <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement<||>
                                                 Iteration_statement8 <$$ term (GLLCombParser.Token "for" Nothing) <** term (GLLCombParser.Token "(" Nothing) <** term (GLLCombParser.Token ";" Nothing) <**> p_Expression <** term (GLLCombParser.Token ";" Nothing) <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement<||>
                                                 Iteration_statement9 <$$ term (GLLCombParser.Token "for" Nothing) <** term (GLLCombParser.Token "(" Nothing) <** term (GLLCombParser.Token ";" Nothing) <** term (GLLCombParser.Token ";" Nothing) <**> p_Expression <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement
p_Jump_statement = "Jump_statement" <:=> Jump_statement1 <$$ term (GLLCombParser.Token "goto" Nothing) <**> p_Identifier <** term (GLLCombParser.Token ";" Nothing)<||>
                                       Jump_statement2 <$$ term (GLLCombParser.Token "continue" Nothing) <** term (GLLCombParser.Token ";" Nothing)<||>
                                       Jump_statement3 <$$ term (GLLCombParser.Token "break" Nothing) <** term (GLLCombParser.Token ";" Nothing)<||>
                                       Jump_statement4 <$$ term (GLLCombParser.Token "return" Nothing) <**> p_Expression <** term (GLLCombParser.Token ";" Nothing)<||>
                                       Jump_statement5 <$$ term (GLLCombParser.Token "return" Nothing) <** term (GLLCombParser.Token ";" Nothing)
p_Labeled_statement = "Labeled_statement" <:=> Labeled_statement1 <$$> p_Identifier <** term (GLLCombParser.Token ":" Nothing) <**> p_Statement<||>
                                             Labeled_statement2 <$$ term (GLLCombParser.Token "case" Nothing) <**> p_Constant_expression <** term (GLLCombParser.Token ":" Nothing) <**> p_Statement<||>
                                             Labeled_statement3 <$$ term (GLLCombParser.Token "default" Nothing) <** term (GLLCombParser.Token ":" Nothing) <**> p_Statement
p_Logical_and_expression = "Logical_and_expression" <:=> Logical_and_expression1 <$$> p_Inclusive_or_expression<||>
                                                       Logical_and_expression2 <$$> p_Logical_and_expression <** term (GLLCombParser.Token "&&" Nothing) <**> p_Inclusive_or_expression
p_Logical_or_expression = "Logical_or_expression" <:=> Logical_or_expression1 <$$> p_Logical_and_expression<||>
                                                     Logical_or_expression2 <$$> p_Logical_or_expression <** term (GLLCombParser.Token "||" Nothing) <**> p_Logical_and_expression
p_Multiplicative_expression = "Multiplicative_expression" <:=> Multiplicative_expression1 <$$> p_Cast_expression<||>
                                                             Multiplicative_expression2 <$$> p_Multiplicative_expression <** term (GLLCombParser.Token "*" Nothing) <**> p_Cast_expression<||>
                                                             Multiplicative_expression3 <$$> p_Multiplicative_expression <** term (GLLCombParser.Token "/" Nothing) <**> p_Cast_expression<||>
                                                             Multiplicative_expression4 <$$> p_Multiplicative_expression <** term (GLLCombParser.Token "%" Nothing) <**> p_Cast_expression
p_Parameter_declaration = "Parameter_declaration" <:=> Parameter_declaration1 <$$> p_Declaration_specifiers <**> p_Declarator<||>
                                                     Parameter_declaration2 <$$> p_Declaration_specifiers <**> p_Abstract_declarator<||>
                                                     Parameter_declaration3 <$$> p_Declaration_specifiers
p_Parameter_list = "Parameter_list" <:=> Parameter_list1 <$$> p_Parameter_declaration<||>
                                       Parameter_list2 <$$> p_Parameter_list <** term (GLLCombParser.Token "," Nothing) <**> p_Parameter_declaration
p_Parameter_type_list = "Parameter_type_list" <:=> Parameter_type_list1 <$$> p_Parameter_list<||>
                                                 Parameter_type_list2 <$$> p_Parameter_list <** term (GLLCombParser.Token "," Nothing) <** term (GLLCombParser.Token "..." Nothing)
p_Pointer = "Pointer" <:=> Pointer1 <$$ term (GLLCombParser.Token "*" Nothing) <**> p_Type_qualifier_list<||>
                         Pointer2 <$$ term (GLLCombParser.Token "*" Nothing)<||>
                         Pointer3 <$$ term (GLLCombParser.Token "*" Nothing) <**> p_Type_qualifier_list <**> p_Pointer<||>
                         Pointer4 <$$ term (GLLCombParser.Token "*" Nothing) <**> p_Pointer
p_Postfix_expression = "Postfix_expression" <:=> Postfix_expression1 <$$> p_Primary_expression<||>
                                               Postfix_expression2 <$$> p_Postfix_expression <** term (GLLCombParser.Token "[" Nothing) <**> p_Expression <** term (GLLCombParser.Token "]" Nothing)<||>
                                               Postfix_expression3 <$$> p_Postfix_expression <** term (GLLCombParser.Token "(" Nothing) <**> p_Argument_expression_list <** term (GLLCombParser.Token ")" Nothing)<||>
                                               Postfix_expression4 <$$> p_Postfix_expression <** term (GLLCombParser.Token "(" Nothing) <** term (GLLCombParser.Token ")" Nothing)<||>
                                               Postfix_expression5 <$$> p_Postfix_expression <** term (GLLCombParser.Token "." Nothing) <**> p_Identifier<||>
                                               Postfix_expression6 <$$> p_Postfix_expression <** term (GLLCombParser.Token "->" Nothing) <**> p_Identifier<||>
                                               Postfix_expression7 <$$> p_Postfix_expression <** term (GLLCombParser.Token "++" Nothing)<||>
                                               Postfix_expression8 <$$> p_Postfix_expression <** term (GLLCombParser.Token "--" Nothing)
p_Primary_expression = "Primary_expression" <:=> Primary_expression1 <$$> p_Identifier<||>
                                               Primary_expression2 <$$> p_Constant<||>
                                               Primary_expression3 <$$> p_Stringlit<||>
                                               Primary_expression4 <$$ term (GLLCombParser.Token "(" Nothing) <**> p_Expression <** term (GLLCombParser.Token ")" Nothing)
p_Relational_expression = "Relational_expression" <:=> Relational_expression1 <$$> p_Shift_expression<||>
                                                     Relational_expression2 <$$> p_Relational_expression <** term (GLLCombParser.Token "<" Nothing) <**> p_Shift_expression<||>
                                                     Relational_expression3 <$$> p_Relational_expression <** term (GLLCombParser.Token ">" Nothing) <**> p_Shift_expression<||>
                                                     Relational_expression4 <$$> p_Relational_expression <** term (GLLCombParser.Token "<=" Nothing) <**> p_Shift_expression<||>
                                                     Relational_expression5 <$$> p_Relational_expression <** term (GLLCombParser.Token ">=" Nothing) <**> p_Shift_expression
p_Selection_statement = "Selection_statement" <:=> Selection_statement1 <$$ term (GLLCombParser.Token "if" Nothing) <** term (GLLCombParser.Token "(" Nothing) <**> p_Expression <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement<||>
                                                 Selection_statement2 <$$ term (GLLCombParser.Token "if" Nothing) <** term (GLLCombParser.Token "(" Nothing) <**> p_Expression <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement <** term (GLLCombParser.Token "else" Nothing) <**> p_Statement<||>
                                                 Selection_statement3 <$$ term (GLLCombParser.Token "switch" Nothing) <** term (GLLCombParser.Token "(" Nothing) <**> p_Expression <** term (GLLCombParser.Token ")" Nothing) <**> p_Statement
p_Shift_expression = "Shift_expression" <:=> Shift_expression1 <$$> p_Additive_expression<||>
                                           Shift_expression2 <$$> p_Shift_expression <** term (GLLCombParser.Token "<<" Nothing) <**> p_Additive_expression<||>
                                           Shift_expression3 <$$> p_Shift_expression <** term (GLLCombParser.Token ">>" Nothing) <**> p_Additive_expression
p_Specifier_qualifier_list = "Specifier_qualifier_list" <:=> Specifier_qualifier_list1 <$$> p_Type_specifier <**> p_Specifier_qualifier_list<||>
                                                           Specifier_qualifier_list2 <$$> p_Type_specifier<||>
                                                           Specifier_qualifier_list3 <$$> p_Type_qualifier <**> p_Specifier_qualifier_list<||>
                                                           Specifier_qualifier_list4 <$$> p_Type_qualifier
p_Statement = "Statement" <:=> Statement1 <$$> p_Labeled_statement<||>
                             Statement2 <$$> p_Expression_statement<||>
                             Statement3 <$$> p_Compound_statement<||>
                             Statement4 <$$> p_Selection_statement<||>
                             Statement5 <$$> p_Iteration_statement<||>
                             Statement6 <$$> p_Jump_statement
p_Statement_list = "Statement_list" <:=> Statement_list1 <$$> p_Statement<||>
                                       Statement_list2 <$$> p_Statement_list <**> p_Statement
p_Storage_class_specifier = "Storage_class_specifier" <:=> Storage_class_specifier1 <$$ term (GLLCombParser.Token "auto" Nothing)<||>
                                                         Storage_class_specifier2 <$$ term (GLLCombParser.Token "register" Nothing)<||>
                                                         Storage_class_specifier3 <$$ term (GLLCombParser.Token "static" Nothing)<||>
                                                         Storage_class_specifier4 <$$ term (GLLCombParser.Token "extern" Nothing)<||>
                                                         Storage_class_specifier5 <$$ term (GLLCombParser.Token "typedef" Nothing)
p_Stringlit = "Stringlit" <:=> Stringlit1 <$$ term (GLLCombParser.Token "STRING" Nothing)<||>
                             Stringlit2 <$$> p_Stringlit <** term (GLLCombParser.Token "STRING" Nothing)
p_Struct_declaration = "Struct_declaration" <:=> Struct_declaration1 <$$> p_Specifier_qualifier_list <**> p_Struct_declarator_list <** term (GLLCombParser.Token ";" Nothing)
p_Struct_declaration_list = "Struct_declaration_list" <:=> Struct_declaration_list1 <$$> p_Struct_declaration<||>
                                                         Struct_declaration_list2 <$$> p_Struct_declaration_list <**> p_Struct_declaration
p_Struct_declarator = "Struct_declarator" <:=> Struct_declarator1 <$$> p_Declarator<||>
                                             Struct_declarator2 <$$> p_Declarator <** term (GLLCombParser.Token ":" Nothing) <**> p_Constant_expression<||>
                                             Struct_declarator3 <$$ term (GLLCombParser.Token ":" Nothing) <**> p_Constant_expression
p_Struct_declarator_list = "Struct_declarator_list" <:=> Struct_declarator_list1 <$$> p_Struct_declarator<||>
                                                       Struct_declarator_list2 <$$> p_Struct_declarator_list <** term (GLLCombParser.Token "," Nothing) <**> p_Struct_declarator
p_Struct_or_union = "Struct_or_union" <:=> Struct_or_union1 <$$ term (GLLCombParser.Token "struct" Nothing)<||>
                                         Struct_or_union2 <$$ term (GLLCombParser.Token "union" Nothing)
p_Struct_or_union_specifier = "Struct_or_union_specifier" <:=> Struct_or_union_specifier1 <$$> p_Struct_or_union <**> p_Identifier <** term (GLLCombParser.Token "{" Nothing) <**> p_Struct_declaration_list <** term (GLLCombParser.Token "}" Nothing)<||>
                                                             Struct_or_union_specifier2 <$$> p_Struct_or_union <** term (GLLCombParser.Token "{" Nothing) <**> p_Struct_declaration_list <** term (GLLCombParser.Token "}" Nothing)<||>
                                                             Struct_or_union_specifier3 <$$> p_Struct_or_union <**> p_Identifier
p_Translation_unit = "Translation_unit" <:=> Translation_unit1 <$$> p_External_declaration<||>
                                           Translation_unit2 <$$> p_Translation_unit <**> p_External_declaration
p_Type_name = "Type_name" <:=> Type_name1 <$$> p_Specifier_qualifier_list <**> p_Abstract_declarator<||>
                             Type_name2 <$$> p_Specifier_qualifier_list
p_Type_qualifier = "Type_qualifier" <:=> Type_qualifier1 <$$ term (GLLCombParser.Token "const" Nothing)<||>
                                       Type_qualifier2 <$$ term (GLLCombParser.Token "volatile" Nothing)
p_Type_qualifier_list = "Type_qualifier_list" <:=> Type_qualifier_list1 <$$> p_Type_qualifier<||>
                                                 Type_qualifier_list2 <$$> p_Type_qualifier_list <**> p_Type_qualifier
p_Type_specifier = "Type_specifier" <:=> Type_specifier1 <$$ term (GLLCombParser.Token "void" Nothing)<||>
                                       Type_specifier10 <$$> p_Struct_or_union_specifier<||>
                                       Type_specifier11 <$$> p_Enum_specifier<||>
                                       Type_specifier12 <$$> p_Typedef_name<||>
                                       Type_specifier2 <$$ term (GLLCombParser.Token "char" Nothing)<||>
                                       Type_specifier3 <$$ term (GLLCombParser.Token "short" Nothing)<||>
                                       Type_specifier4 <$$ term (GLLCombParser.Token "int" Nothing)<||>
                                       Type_specifier5 <$$ term (GLLCombParser.Token "long" Nothing)<||>
                                       Type_specifier6 <$$ term (GLLCombParser.Token "float" Nothing)<||>
                                       Type_specifier7 <$$ term (GLLCombParser.Token "double" Nothing)<||>
                                       Type_specifier8 <$$ term (GLLCombParser.Token "signed" Nothing)<||>
                                       Type_specifier9 <$$ term (GLLCombParser.Token "unsigned" Nothing)
p_Typedef_name = "Typedef_name" <:=> Typedef_name1 <$$ term (GLLCombParser.Token "ID" Nothing)<||>
                                   Typedef_name2 <$$ term (GLLCombParser.Token "TYPE_ID" Nothing)
p_Unary_expression = "Unary_expression" <:=> Unary_expression1 <$$> p_Postfix_expression<||>
                                           Unary_expression2 <$$ term (GLLCombParser.Token "++" Nothing) <**> p_Unary_expression<||>
                                           Unary_expression3 <$$ term (GLLCombParser.Token "--" Nothing) <**> p_Unary_expression<||>
                                           Unary_expression4 <$$> p_Unary_operator <**> p_Cast_expression<||>
                                           Unary_expression5 <$$ term (GLLCombParser.Token "sizeof" Nothing) <**> p_Unary_expression<||>
                                           Unary_expression6 <$$ term (GLLCombParser.Token "sizeof" Nothing) <** term (GLLCombParser.Token "(" Nothing) <**> p_Type_name <** term (GLLCombParser.Token ")" Nothing)
p_Unary_operator = "Unary_operator" <:=> Unary_operator1 <$$ term (GLLCombParser.Token "&" Nothing)<||>
                                               Unary_operator2 <$$ term (GLLCombParser.Token "*" Nothing)<||>
                                               Unary_operator3 <$$ term (GLLCombParser.Token "+" Nothing)<||>
                                               Unary_operator4 <$$ term (GLLCombParser.Token "-" Nothing)<||>
                                               Unary_operator5 <$$ term (GLLCombParser.Token "~" Nothing)<||>
                                               Unary_operator6 <$$ term (GLLCombParser.Token "!" Nothing)

parse :: [GLLCombParser.Token] -> IO () 
parse ts = do 
  Lib.printParseDataWithOptions [] [] p_Translation_unit ts
--  Lib.printParseDataWithOptions [noSelectTest] [] p_Translation_unit ts

data Token = Token String (Maybe String) | EOS | EPS
    deriving (Show, Ord, Eq)

instance Parseable GLLCombParser.Token where
  eos = GLLCombParser.EOS
  eps = GLLCombParser.EPS

  unlex (GLLCombParser.Token s _) = s
  unlex (GLLCombParser.EOS)       = "$"
  unlex (GLLCombParser.EPS)       = "#"
  matches = mut_matches

(GLLCombParser.Token t1 _) `mut_matches` (GLLCombParser.Token t2 _) = t1 == t2
GLLCombParser.EOS `mut_matches` GLLCombParser.EOS = True
GLLCombParser.EPS `mut_matches` GLLCombParser.EPS = False
_ `mut_matches` _ = False

term = flip term_parser id
