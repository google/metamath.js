include "csiga.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cpw.mm"
include "cint.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "sigasspw.mm"
include "selpw.mm"
include "sylibr.mm"
include "crn.mm"
include "cuni.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wne.mm"
include "elrnsiga.mm"
include "adantr.mm"
include "eldifsn.mm"
include "biimpi.mm"
include "adantl.mm"
include "simpld.mm"
include "elin1d.mm"
include "elin2d.mm"
include "fict.mm"
include "syl.mm"
include "simprd.mm"
include "sigaclci.mm"
include "syl22anc.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ispisys2.mm"
include "ssriv.mm"

theorem sigapisys
  let cP: class P
  let cO: class O
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cA: class A
  let cB: class B
  assume ispisys.p: |- P = { s e. ~P ~P O | ( fi ` s ) C_ s }

  disjoint O s
  disjoint O t
  disjoint O x
  disjoint O y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint P t
  disjoint A x
  disjoint B x
  disjoint P x
  assert |- ( sigAlgebra ` O ) C_ P

  proof
    vt
    cO
    csiga
    cfv
    #
    cP
    vt
    cv
    #
    @0
    wcel
    #
    @1
    cO
    cpw
    #
    cpw
    wcel
    #
    vx
    cv
    #
    cint
    @1
    wcel
    #
    vx
    @1
    cpw
    #
    cfn
    cin
    #
    c0
    csn
    cdif
    #
    wral
    #
    wa
    @1
    cP
    wcel
    @2
    @4
    @10
    @2
    @1
    @3
    wss
    @4
    cO
    @1
    sigasspw
    vt
    @3
    selpw
    sylibr
    @2
    @6
    vx
    @9
    @2
    @5
    @9
    wcel
    #
    wa
    #
    @1
    csiga
    crn
    cuni
    wcel
    #
    @5
    @7
    wcel
    @5
    com
    cdom
    wbr
    #
    @5
    c0
    wne
    #
    @6
    @2
    @13
    @11
    @1
    cO
    elrnsiga
    adantr
    @12
    @7
    cfn
    @5
    @12
    @5
    @8
    wcel
    #
    @15
    @11
    @16
    @15
    wa
    #
    @2
    @11
    @17
    @5
    @8
    c0
    eldifsn
    biimpi
    adantl
    #
    simpld
    #
    elin1d
    @12
    @5
    cfn
    wcel
    @14
    @12
    @7
    cfn
    @5
    @19
    elin2d
    @5
    fict
    syl
    @12
    @16
    @15
    @18
    simprd
    @5
    @1
    sigaclci
    syl22anc
    ralrimiva
    jca
    vx
    cP
    @1
    cO
    vs
    ispisys.p
    ispisys2
    sylibr
    ssriv
end
