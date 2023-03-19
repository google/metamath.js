include "csumge0.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "csu.mm"
include "cmpt.mm"
include "crn.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wceq.mm"
include "simpl.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "w3a.mm"
include "simp3.mm"
include "adantr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "wn.mm"
include "sge0rern.mm"
include "fge0iccico.mm"
include "wss.mm"
include "elpwinss.mm"
include "elinel2.mm"
include "fsumlesge0.mm"
include "3adant3.mm"
include "eqbrtrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "sylc.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem sge0rnbnd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cF: class F
  let cV: class V
  let cX: class X
  let vk: setvar k
  assume sge0rnbnd.x: |- ( ph -> X e. V )
  assume sge0rnbnd.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0rnbnd.re: |- ( ph -> ( sum^ ` F ) e. RR )

  disjoint F w
  disjoint F x
  disjoint F z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint F y
  disjoint x y
  disjoint y z
  disjoint X z
  disjoint ph w
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. z e. RR A. w e. ran ( x e. ( ~P X i^i Fin ) |-> sum_ y e. x ( F ` y ) ) w <_ z )

  proof
    wph
    cF
    csumge0
    cfv
    #
    cr
    wcel
    vw
    cv
    #
    @0
    cle
    wbr
    #
    vw
    vx
    cX
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    vy
    cv
    cF
    cfv
    vy
    csu
    #
    cmpt
    #
    crn
    #
    wral
    #
    @1
    vz
    cv
    #
    cle
    wbr
    #
    vw
    @8
    wral
    #
    vz
    cr
    wrex
    sge0rnbnd.re
    wph
    @2
    vw
    @8
    wph
    @1
    @8
    wcel
    #
    wa
    wph
    @1
    @6
    wceq
    #
    vx
    @4
    wrex
    #
    @2
    wph
    @13
    simpl
    @13
    @15
    wph
    @13
    @15
    @1
    cvv
    wcel
    @13
    @15
    wb
    vw
    vex
    vx
    @4
    @6
    @1
    @7
    cvv
    @7
    eqid
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @14
    @2
    vx
    @4
    wph
    @5
    @4
    wcel
    #
    @14
    @2
    wph
    @16
    @14
    w3a
    @1
    @6
    @0
    cle
    wph
    @16
    @14
    simp3
    wph
    @16
    @6
    @0
    cle
    wbr
    @14
    wph
    @16
    wa
    #
    vy
    cF
    cV
    cX
    @5
    wph
    cX
    cV
    wcel
    @16
    sge0rnbnd.x
    adantr
    @17
    cF
    cX
    wph
    cX
    cc0
    cpnf
    cicc
    co
    cF
    wf
    @16
    sge0rnbnd.f
    adantr
    wph
    cpnf
    cF
    crn
    wcel
    wn
    @16
    wph
    cF
    cV
    cX
    sge0rnbnd.x
    sge0rnbnd.f
    sge0rnbnd.re
    sge0rern
    adantr
    fge0iccico
    @16
    @5
    cX
    wss
    wph
    @5
    cX
    cfn
    elpwinss
    adantl
    @16
    @5
    cfn
    wcel
    wph
    @5
    @3
    cfn
    elinel2
    adantl
    fsumlesge0
    3adant3
    eqbrtrd
    3exp
    rexlimdv
    sylc
    ralrimiva
    @12
    @9
    vz
    @0
    cr
    @10
    @0
    wceq
    @11
    @2
    vw
    @8
    @10
    @0
    @1
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
end
