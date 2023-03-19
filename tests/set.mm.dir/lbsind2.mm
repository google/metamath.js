include "clmod.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "lbsel.mm"
include "syl2anc.mm"
include "lmodvs1.mm"
include "wn.mm"
include "crg.mm"
include "lmodring.mm"
include "ringidcl.mm"
include "3syl.mm"
include "simp1r.mm"
include "lbsind.mm"
include "syl22anc.mm"
include "eqneltrrd.mm"

theorem lbsind2
  let cB: class B
  let c.1: class .1.
  let cE: class E
  let cF: class F
  let cJ: class J
  let cN: class N
  let cW: class W
  let c.0: class .0.
  assume lbsind2.j: |- J = ( LBasis ` W )
  assume lbsind2.n: |- N = ( LSpan ` W )
  assume lbsind2.f: |- F = ( Scalar ` W )
  assume lbsind2.o: |- .1. = ( 1r ` F )
  assume lbsind2.z: |- .0. = ( 0g ` F )


  assert |- ( ( ( W e. LMod /\ .1. =/= .0. ) /\ B e. J /\ E e. B ) -> -. E e. ( N ` ( B \ { E } ) ) )

  proof
    cW
    clmod
    wcel
    #
    c.1
    c.0
    wne
    #
    wa
    #
    cB
    cJ
    wcel
    #
    cE
    cB
    wcel
    #
    w3a
    #
    c.1
    cE
    cW
    cvsca
    cfv
    #
    co
    #
    cE
    cB
    cE
    csn
    cdif
    cN
    cfv
    #
    @5
    @0
    cE
    cW
    cbs
    cfv
    #
    wcel
    #
    @7
    cE
    wceq
    @0
    @1
    @3
    @4
    simp1l
    #
    @5
    @3
    @4
    @10
    @2
    @3
    @4
    simp2
    #
    @2
    @3
    @4
    simp3
    #
    cB
    cE
    cJ
    @9
    cW
    @9
    eqid
    #
    lbsind2.j
    lbsel
    syl2anc
    @6
    c.1
    cF
    @9
    cW
    cE
    @14
    lbsind2.f
    @6
    eqid
    #
    lbsind2.o
    lmodvs1
    syl2anc
    @5
    @3
    @4
    c.1
    cF
    cbs
    cfv
    #
    wcel
    #
    @1
    @7
    @8
    wcel
    wn
    @12
    @13
    @5
    @0
    cF
    crg
    wcel
    @17
    @11
    cF
    cW
    lbsind2.f
    lmodring
    @16
    cF
    c.1
    @16
    eqid
    #
    lbsind2.o
    ringidcl
    3syl
    @0
    @1
    @3
    @4
    simp1r
    c.1
    cB
    @6
    cE
    cF
    cJ
    @16
    cN
    @9
    cW
    c.0
    @14
    lbsind2.j
    lbsind2.n
    lbsind2.f
    @15
    @18
    lbsind2.z
    lbsind
    syl22anc
    eqneltrrd
end
