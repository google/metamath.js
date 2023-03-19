include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "w3a.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cascl.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "cmgp.mm"
include "cmg.mm"
include "cv1.mm"
include "eqid.mm"
include "ply1sclrmsm.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "coe1sclmulfv.mm"
include "eqtrd.mm"

theorem coe1sclmulval
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cK: class K
  let cN: class N
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume coe1sclmulval.p: |- P = ( Poly1 ` R )
  assume coe1sclmulval.b: |- B = ( Base ` P )
  assume coe1sclmulval.k: |- K = ( Base ` R )
  assume coe1sclmulval.a: |- A = ( algSc ` P )
  assume coe1sclmulval.s: |- S = ( .s ` P )
  assume coe1sclmulval.t: |- .xb = ( .r ` P )
  assume coe1sclmulval.u: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ ( Y e. K /\ Z e. B ) /\ N e. NN0 ) -> ( ( coe1 ` ( Y S Z ) ) ` N ) = ( Y .x. ( ( coe1 ` Z ) ` N ) ) )

  proof
    cR
    crg
    wcel
    #
    cY
    cK
    wcel
    #
    cZ
    cB
    wcel
    #
    wa
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cN
    cY
    cZ
    cS
    co
    #
    cco1
    cfv
    #
    cfv
    cN
    cY
    cP
    cascl
    cfv
    #
    cfv
    cZ
    c.xb
    co
    #
    cco1
    cfv
    #
    cfv
    cY
    cN
    cZ
    cco1
    cfv
    cfv
    c.x
    co
    @5
    cN
    @7
    @10
    @5
    @6
    @9
    cco1
    @5
    @9
    @6
    @5
    @0
    @1
    @2
    @9
    @6
    wceq
    @0
    @3
    @4
    simp1
    @0
    @1
    @2
    @4
    simp2l
    @0
    @1
    @2
    @4
    simp2r
    @8
    cP
    cR
    cS
    c.xb
    cB
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    #
    cY
    cK
    @11
    cR
    cv1
    cfv
    #
    cZ
    coe1sclmulval.k
    coe1sclmulval.p
    coe1sclmulval.b
    @13
    eqid
    coe1sclmulval.s
    coe1sclmulval.t
    @11
    eqid
    @12
    eqid
    @8
    eqid
    #
    ply1sclrmsm
    syl3anc
    eqcomd
    fveq2d
    fveq1d
    @8
    cB
    cP
    cR
    c.xb
    c.x
    cK
    cY
    cZ
    cN
    coe1sclmulval.p
    coe1sclmulval.b
    coe1sclmulval.k
    @14
    coe1sclmulval.t
    coe1sclmulval.u
    coe1sclmulfv
    eqtrd
end
