include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cdiv.mm"
include "cof.mm"
include "co.mm"
include "cc0.mm"
include "csupp.mm"
include "cres.mm"
include "cfdiv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-fdiv.mm"
include "a1i.mm"
include "oveq12.mm"
include "oveq1.mm"
include "adantl.mm"
include "reseq12d.mm"
include "elex.mm"
include "adantr.mm"
include "wfun.mm"
include "cdm.mm"
include "cin.mm"
include "cfv.mm"
include "cmpt.mm"
include "funmpt.mm"
include "offval0.mm"
include "funeqd.mm"
include "mpbiri.mm"
include "ovex.mm"
include "resfunexg.mm"
include "sylancl.mm"
include "ovmpt2d.mm"

theorem fdivval
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( F e. V /\ G e. W ) -> ( F /_f G ) = ( ( F oF / G ) |` ( G supp 0 ) ) )

  proof
    cF
    cV
    wcel
    #
    cG
    cW
    wcel
    #
    wa
    #
    vf
    vg
    cF
    cG
    cvv
    cvv
    vf
    cv
    #
    vg
    cv
    #
    cdiv
    cof
    #
    co
    #
    @4
    cc0
    csupp
    co
    #
    cres
    #
    cF
    cG
    @5
    co
    #
    cG
    cc0
    csupp
    co
    #
    cres
    #
    cfdiv
    cvv
    cfdiv
    vf
    vg
    cvv
    cvv
    @8
    cmpt2
    wceq
    @2
    vf
    vg
    df-fdiv
    a1i
    @3
    cF
    wceq
    #
    @4
    cG
    wceq
    #
    wa
    #
    @8
    @11
    wceq
    @2
    @14
    @6
    @9
    @7
    @10
    @3
    cF
    @4
    cG
    @5
    oveq12
    @13
    @7
    @10
    wceq
    @12
    @4
    cG
    cc0
    csupp
    oveq1
    adantl
    reseq12d
    adantl
    @0
    cF
    cvv
    wcel
    @1
    cF
    cV
    elex
    adantr
    @1
    cG
    cvv
    wcel
    @0
    cG
    cW
    elex
    adantl
    @2
    @9
    wfun
    #
    @10
    cvv
    wcel
    @11
    cvv
    wcel
    @2
    @15
    vx
    cF
    cdm
    cG
    cdm
    cin
    #
    vx
    cv
    #
    cF
    cfv
    @17
    cG
    cfv
    cdiv
    co
    #
    cmpt
    #
    wfun
    vx
    @16
    @18
    funmpt
    @2
    @9
    @19
    vx
    cdiv
    cF
    cG
    cV
    cW
    offval0
    funeqd
    mpbiri
    cG
    cc0
    csupp
    ovex
    @9
    @10
    cvv
    resfunexg
    sylancl
    ovmpt2d
end
