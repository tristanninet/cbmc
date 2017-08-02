/*******************************************************************\

 Module: Unit tests for calculate_max_string_length in
   solvers/refinement/string_constraint_generator_valueof.cpp

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <solvers/refinement/string_constraint_generator.h>
#include <util/std_types.h>


size_t expected_length(const int radix, const typet &type)
{
  std::string longest("");
  if(radix==2)
  {
    if(type==unsignedbv_typet(32))
    {
      longest="11111111111111111111111111111111";
    }
    else if(type==unsignedbv_typet(64))
    {
      longest=
        "1111111111111111111111111111111111111111111111111111111111111111";
    }
    else if(type==signedbv_typet(32))
    {
      longest="-10000000000000000000000000000000";
    }
    else if(type==signedbv_typet(64))
    {
      longest=
        "-1000000000000000000000000000000000000000000000000000000000000000";
    }
  }
  else if(radix==8)
  {
    if(type==unsignedbv_typet(32))
    {
      longest="37777777777";
    }
    else if(type==unsignedbv_typet(64))
    {
      longest=
        "1777777777777777777777";
    }
    else if(type==signedbv_typet(32))
    {
      longest="-20000000000";
    }
    else if(type==signedbv_typet(64))
    {
      longest=
        "-1000000000000000000000";
    }
  }
  else if(radix==10)
  {
    if(type==unsignedbv_typet(32))
    {
      longest="4294967295";
    }
    else if(type==unsignedbv_typet(64))
    {
      longest=
        "18446744073709551615";
    }
    else if(type==signedbv_typet(32))
    {
      longest="-2147483648";
    }
    else if(type==signedbv_typet(64))
    {
      longest=
        "-9223372036854775808";
    }
  }
  else if(radix==16)
  {
    if(type==unsignedbv_typet(32))
    {
      longest="ffffffff";
    }
    else if(type==unsignedbv_typet(64))
    {
      longest=
        "ffffffffffffffff";
    }
    else if(type==signedbv_typet(32))
    {
      longest="-80000000";
    }
    else if(type==signedbv_typet(64))
    {
      longest=
        "-8000000000000000";
    }
  }

  return longest.size();
}

SCENARIO("calculate_max_string_length",
  "[core][solvers][refinement][string_constraint_generator_valueof]")
{
  const int radixes[]={2, 8, 10, 16};
  const typet int_types[]={
    signedbv_typet(32),
    unsignedbv_typet(32),
    signedbv_typet(64),
    unsignedbv_typet(64)};

  for(const int radix : radixes)
  {
    WHEN(std::string("radix = ")+std::to_string(radix))
    {
      for(const typet &type : int_types)
      {
        WHEN(std::string("type = ")+type.pretty())
        {
          double radix_d=static_cast<double>(radix);
          size_t actual_value=calculate_max_string_length(type, radix_d);
          size_t expected_value=expected_length(radix, type);
          /// Due to floating point rounding errors, we sometime get one more
          /// than the actual value, which is perfectly fine for our purposes
          REQUIRE(expected_value<=actual_value);
          REQUIRE(expected_value+1>=actual_value);
        }
      }
    }
  }
}