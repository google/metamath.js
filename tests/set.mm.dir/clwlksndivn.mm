include "cfusgr.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "c1st.mm"
include "wceq.mm"
include "cclwlks.mm"
include "crab.mm"
include "cdvds.mm"
include "clwwlkndivn.mm"
include "clwlkssizeeq.mm"
include "breqtrd.mm"

theorem clwlksndivn
  let cG: class G
  let cN: class N
  let vc: setvar c

  disjoint G c
  disjoint N c
  assert |- ( ( G e. FinUSGraph /\ N e. Prime ) -> N || ( # ` { c e. ( ClWalks ` G ) | ( # ` ( 1st ` c ) ) = N } ) )

  proof
    cG
    cfusgr
    wcel
    cN
    cprime
    wcel
    wa
    cN
    cN
    cG
    cclwwlkn
    co
    chash
    cfv
    vc
    cv
    c1st
    cfv
    chash
    cfv
    cN
    wceq
    vc
    cG
    cclwlks
    cfv
    crab
    chash
    cfv
    cdvds
    cG
    cN
    clwwlkndivn
    cG
    cN
    vc
    clwlkssizeeq
    breqtrd
end
