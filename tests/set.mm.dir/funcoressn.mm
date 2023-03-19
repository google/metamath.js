include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "wfn.mm"
include "ccom.mm"
include "crn.mm"
include "wceq.mm"
include "wi.mm"
include "dmressnsn.mm"
include "df-fn.mm"
include "simplbi2com.mm"
include "syl.mm"
include "imp.mm"
include "adantr.mm"
include "cima.mm"
include "fnsnfv.mm"
include "adantl.mm"
include "df-ima.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "fneq12d.mm"
include "mpbid.mm"
include "fnfun.mm"
include "funres.mm"
include "funfn.mm"
include "sylib.mm"
include "fnresfnco.mm"
include "syl2anc.mm"
include "resco.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funcoressn
  let cA: class A
  let cF: class F
  let cG: class G
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( ( G ` X ) e. dom F /\ Fun ( F |` { ( G ` X ) } ) ) /\ ( G Fn A /\ X e. A ) ) -> Fun ( ( F o. G ) |` { X } ) )

  proof
    cX
    cG
    cfv
    #
    cF
    cdm
    wcel
    #
    cF
    @0
    csn
    #
    cres
    #
    wfun
    #
    wa
    #
    cG
    cA
    wfn
    #
    cX
    cA
    wcel
    #
    wa
    #
    wa
    #
    cF
    cG
    cX
    csn
    #
    cres
    #
    ccom
    #
    wfun
    #
    cF
    cG
    ccom
    @10
    cres
    #
    wfun
    @9
    @12
    @11
    cdm
    #
    wfn
    #
    @13
    @9
    cF
    @11
    crn
    #
    cres
    #
    @17
    wfn
    #
    @11
    @15
    wfn
    #
    @16
    @9
    @3
    @2
    wfn
    #
    @19
    @5
    @21
    @8
    @1
    @4
    @21
    @1
    @3
    cdm
    @2
    wceq
    #
    @4
    @21
    wi
    @0
    cF
    dmressnsn
    @21
    @4
    @22
    @3
    @2
    df-fn
    simplbi2com
    syl
    imp
    adantr
    @9
    @2
    @17
    @3
    @18
    @9
    @2
    @17
    cF
    @9
    @2
    cG
    @10
    cima
    #
    @17
    @8
    @2
    @23
    wceq
    @5
    cA
    cX
    cG
    fnsnfv
    adantl
    cG
    @10
    df-ima
    syl6eq
    #
    reseq2d
    @24
    fneq12d
    mpbid
    @8
    @20
    @5
    @6
    @20
    @7
    @6
    cG
    wfun
    #
    @20
    cA
    cG
    fnfun
    @25
    @11
    wfun
    @20
    @10
    cG
    funres
    @11
    funfn
    sylib
    syl
    adantr
    adantl
    @15
    cF
    @11
    fnresfnco
    syl2anc
    @15
    @12
    fnfun
    syl
    @14
    @12
    cF
    cG
    @10
    resco
    funeqi
    sylibr
end
