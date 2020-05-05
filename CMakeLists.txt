cmake_minimum_required(VERSION 3.5)
project(swipl-clpqr)

include("../cmake/PrologPackage.cmake")

set(CLPRPRIV bb_r.pl bv_r.pl fourmotz_r.pl ineq_r.pl itf_r.pl nf_r.pl store_r.pl)
set(CLPQPRIV bb_q.pl bv_q.pl fourmotz_q.pl ineq_q.pl itf_q.pl nf_q.pl store_q.pl)
set(CLPQRPRIV class.pl dump.pl geler.pl itf.pl ordering.pl project.pl
    redund.pl highlight.pl)

prepend(CLPRPRIV  clpr/  ${CLPRPRIV})
prepend(CLPQPRIV  clpq/  ${CLPQPRIV})
prepend(CLPQRPRIV clpqr/ ${CLPQRPRIV})

swipl_plugin(clpqr
	     PL_LIB_SUBDIR clp
	     PL_LIBS clpr.pl clpq.pl)
swipl_plugin(clpq_priv
	     NOINDEX
	     PL_LIB_SUBDIR clp/clpq
	     PL_LIBS ${CLPQPRIV})
swipl_plugin(clpr_priv
	     NOINDEX
	     PL_LIB_SUBDIR clp/clpr
	     PL_LIBS ${CLPRPRIV})
swipl_plugin(clpqr_priv
	     NOINDEX
	     PL_LIB_SUBDIR clp/clpqr
	     PL_LIBS ${CLPQRPRIV})
