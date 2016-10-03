#include <cegis/facade/runner_helper.h>
#include <cegis/symex/cegis_symex_learn.h>
#include <cegis/symex/cegis_symex_verify.h>
#include <cegis/refactor/preprocessing/refactor_preprocessing.h>
#include <cegis/refactor/learn/refactor_symex_learn.h>
#include <cegis/refactor/verify/refactor_symex_verify.h>
#include <cegis/refactor/facade/refactor_runner.h>

int run_refactor(optionst &options, messaget::mstreamt &result,
    const symbol_tablet &st, const goto_functionst &gf)
{
  refactor_preprocessingt preproc;
  refactor_symex_learnt learn_cfg;
  refactor_symex_verifyt verify_cfg;
  cegis_symex_learnt<refactor_preprocessingt, refactor_symex_learnt> learn(
      options, preproc, learn_cfg);
  refactor_symex_verifyt vcfg;
  cegis_symex_verifyt<refactor_symex_verifyt> oracle(options, verify_cfg);
  return run_cegis_with_statistics_wrapper(
      result, options, learn, oracle, preproc);
}
