include "ccnv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "crab.mm"
include "cima.mm"
include "corvc.mm"
include "co.mm"
include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "wf.mm"
include "rrvf2.mm"
include "ffun.mm"
include "syl.mm"
include "wcel.mm"
include "w3a.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "letrd.mm"
include "3expia.mm"
include "ss2rabdv.mm"
include "sspreima.mm"
include "syl2anc.mm"
include "orrvcval4.mm"
include "3sstr4d.mm"

theorem orvclteinc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cX: class X
  let vx: setvar x
  assume dstfrv.1: |- ( ph -> P e. Prob )
  assume dstfrv.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume orvclteinc.1: |- ( ph -> A e. RR )
  assume orvclteinc.2: |- ( ph -> B e. RR )
  assume orvclteinc.3: |- ( ph -> A <_ B )


  assert |- ( ph -> ( X oRVC <_ A ) C_ ( X oRVC <_ B ) )

  proof
    wph
    cX
    ccnv
    #
    vx
    cv
    #
    cA
    cle
    wbr
    #
    vx
    cr
    crab
    #
    cima
    #
    @0
    @1
    cB
    cle
    wbr
    #
    vx
    cr
    crab
    #
    cima
    #
    cX
    cA
    cle
    corvc
    #
    co
    cX
    cB
    @8
    co
    wph
    cX
    wfun
    #
    @3
    @6
    wss
    @4
    @7
    wss
    wph
    cX
    cdm
    #
    cr
    cX
    wf
    @9
    wph
    cP
    cX
    dstfrv.1
    dstfrv.2
    rrvf2
    @10
    cr
    cX
    ffun
    syl
    wph
    @2
    @5
    vx
    cr
    wph
    @1
    cr
    wcel
    #
    @2
    @5
    wph
    @11
    @2
    w3a
    @1
    cA
    cB
    wph
    @11
    @2
    simp2
    wph
    @11
    cA
    cr
    wcel
    @2
    orvclteinc.1
    3ad2ant1
    wph
    @11
    cB
    cr
    wcel
    @2
    orvclteinc.2
    3ad2ant1
    wph
    @11
    @2
    simp3
    wph
    @11
    cA
    cB
    cle
    wbr
    @2
    orvclteinc.3
    3ad2ant1
    letrd
    3expia
    ss2rabdv
    @3
    @6
    cX
    sspreima
    syl2anc
    wph
    vx
    cA
    cP
    cle
    cr
    cX
    dstfrv.1
    dstfrv.2
    orvclteinc.1
    orrvcval4
    wph
    vx
    cB
    cP
    cle
    cr
    cX
    dstfrv.1
    dstfrv.2
    orvclteinc.2
    orrvcval4
    3sstr4d
end
