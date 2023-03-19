include "clnm.mm"
include "wcel.mm"
include "clmod.mm"
include "cv.mm"
include "cress.mm"
include "co.mm"
include "clfig.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "islnm.mm"
include "eqid.mm"
include "islssfg2.mm"
include "eqcom.mm"
include "rexbii.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem islnm2
  let cB: class B
  let cS: class S
  let vg: setvar g
  let vi: setvar i
  let cM: class M
  let cN: class N
  assume islnm2.b: |- B = ( Base ` M )
  assume islnm2.s: |- S = ( LSubSp ` M )
  assume islnm2.n: |- N = ( LSpan ` M )

  disjoint g i
  disjoint M i
  disjoint M g
  disjoint N i
  disjoint N g
  disjoint S i
  disjoint S g
  disjoint B i
  disjoint B g
  assert |- ( M e. LNoeM <-> ( M e. LMod /\ A. i e. S E. g e. ( ~P B i^i Fin ) i = ( N ` g ) ) )

  proof
    cM
    clnm
    wcel
    cM
    clmod
    wcel
    #
    cM
    vi
    cv
    #
    cress
    co
    #
    clfig
    wcel
    #
    vi
    cS
    wral
    #
    wa
    @0
    @1
    vg
    cv
    cN
    cfv
    #
    wceq
    #
    vg
    cB
    cpw
    cfn
    cin
    #
    wrex
    #
    vi
    cS
    wral
    #
    wa
    cS
    vi
    cM
    islnm2.s
    islnm
    @0
    @4
    @9
    @0
    @3
    @8
    vi
    cS
    @0
    @1
    cS
    wcel
    wa
    @3
    @5
    @1
    wceq
    #
    vg
    @7
    wrex
    @8
    cB
    cS
    @1
    cN
    cM
    @2
    vg
    @2
    eqid
    islnm2.s
    islnm2.n
    islnm2.b
    islssfg2
    @10
    @6
    vg
    @7
    @5
    @1
    eqcom
    rexbii
    syl6bb
    ralbidva
    pm5.32i
    bitri
end
