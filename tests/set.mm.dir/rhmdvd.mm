include "crh.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wa.mm"
include "cmulr.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "eqid.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "simp22.mm"
include "oveq12d.mm"
include "crg.mm"
include "cbs.mm"
include "rhmrcl2.mm"
include "3ad2ant1.mm"
include "wf.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "simp3l.mm"
include "simp3r.mm"
include "dvrcan5.mm"
include "syl13anc.mm"
include "eqtr2d.mm"

theorem rhmdvd
  let cA: class A
  let cB: class B
  let cC: class C
  let c.dv: class ./
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cX: class X
  assume rhmdvd.u: |- U = ( Unit ` S )
  assume rhmdvd.x: |- X = ( Base ` R )
  assume rhmdvd.d: |- ./ = ( /r ` S )
  assume rhmdvd.m: |- .x. = ( .r ` R )


  assert |- ( ( F e. ( R RingHom S ) /\ ( A e. X /\ B e. X /\ C e. X ) /\ ( ( F ` B ) e. U /\ ( F ` C ) e. U ) ) -> ( ( F ` A ) ./ ( F ` B ) ) = ( ( F ` ( A .x. C ) ) ./ ( F ` ( B .x. C ) ) ) )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    cB
    cF
    cfv
    #
    cU
    wcel
    #
    cC
    cF
    cfv
    #
    cU
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cC
    c.x
    co
    cF
    cfv
    #
    cB
    cC
    c.x
    co
    cF
    cfv
    #
    c.dv
    co
    cA
    cF
    cfv
    #
    @7
    cS
    cmulr
    cfv
    #
    co
    #
    @5
    @7
    @14
    co
    #
    c.dv
    co
    #
    @13
    @5
    c.dv
    co
    #
    @10
    @11
    @15
    @12
    @16
    c.dv
    @10
    @0
    @1
    @3
    @11
    @15
    wceq
    @0
    @4
    @9
    simp1
    #
    @0
    @1
    @2
    @3
    @9
    simp21
    #
    @0
    @1
    @2
    @3
    @9
    simp23
    #
    cA
    cC
    cR
    cS
    c.x
    @14
    cF
    cX
    rhmdvd.x
    rhmdvd.m
    @14
    eqid
    #
    rhmmul
    syl3anc
    @10
    @0
    @2
    @3
    @12
    @16
    wceq
    @19
    @0
    @1
    @2
    @3
    @9
    simp22
    @21
    cB
    cC
    cR
    cS
    c.x
    @14
    cF
    cX
    rhmdvd.x
    rhmdvd.m
    @22
    rhmmul
    syl3anc
    oveq12d
    @10
    cS
    crg
    wcel
    #
    @13
    cS
    cbs
    cfv
    #
    wcel
    @6
    @8
    @17
    @18
    wceq
    @0
    @4
    @23
    @9
    cR
    cS
    cF
    rhmrcl2
    3ad2ant1
    @10
    cX
    @24
    cA
    cF
    @0
    @4
    cX
    @24
    cF
    wf
    @9
    cX
    @24
    cR
    cS
    cF
    rhmdvd.x
    @24
    eqid
    #
    rhmf
    3ad2ant1
    @20
    ffvelrnd
    @0
    @4
    @6
    @8
    simp3l
    @0
    @4
    @6
    @8
    simp3r
    @24
    c.dv
    cS
    @14
    cU
    @13
    @5
    @7
    @25
    rhmdvd.u
    rhmdvd.d
    @22
    dvrcan5
    syl13anc
    eqtr2d
end
