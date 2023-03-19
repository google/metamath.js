include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cr.mm"
include "co.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr1.mm"
include "rexrd.mm"
include "simpr2.mm"
include "resubcld.mm"
include "simpr3.mm"
include "xmetlecl.mm"
include "syl122anc.mm"
include "cxne.mm"
include "cxad.mm"
include "wceq.mm"
include "rexsub.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "xblss2.mm"

theorem blss2
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cX: class X
  let cA: class A
  let vx: setvar x
  let vr: setvar r
  let vy: setvar y
  let wph: wff ph


  assert |- ( ( ( D e. ( *Met ` X ) /\ P e. X /\ Q e. X ) /\ ( R e. RR /\ S e. RR /\ ( P D Q ) <_ ( S - R ) ) ) -> ( P ( ball ` D ) R ) C_ ( Q ( ball ` D ) S ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cQ
    cX
    wcel
    #
    w3a
    #
    cR
    cr
    wcel
    #
    cS
    cr
    wcel
    #
    cP
    cQ
    cD
    co
    #
    cS
    cR
    cmin
    co
    #
    cle
    wbr
    #
    w3a
    #
    wa
    #
    cD
    cP
    cQ
    cR
    cS
    cX
    @0
    @1
    @2
    @9
    simpl1
    #
    @0
    @1
    @2
    @9
    simpl2
    #
    @0
    @1
    @2
    @9
    simpl3
    #
    @10
    cR
    @3
    @4
    @5
    @8
    simpr1
    #
    rexrd
    @10
    cS
    @3
    @4
    @5
    @8
    simpr2
    #
    rexrd
    @10
    @0
    @1
    @2
    @7
    cr
    wcel
    @8
    @6
    cr
    wcel
    @11
    @12
    @13
    @10
    cS
    cR
    @15
    @14
    resubcld
    @3
    @4
    @5
    @8
    simpr3
    #
    cP
    cQ
    @7
    cD
    cX
    xmetlecl
    syl122anc
    @10
    @6
    @7
    cS
    cR
    cxne
    cxad
    co
    #
    cle
    @16
    @10
    @5
    @4
    @17
    @7
    wceq
    @15
    @14
    cS
    cR
    rexsub
    syl2anc
    breqtrrd
    xblss2
end
