include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cn0.mm"
include "wa.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cof.mm"
include "wceq.mm"
include "coe1add.mm"
include "adantr.mm"
include "fveq1d.mm"
include "wfn.mm"
include "cvv.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "coe1f.mm"
include "ffn.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "nn0ex.mm"
include "a1i.mm"
include "simpr.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "eqtrd.mm"

theorem coe1addfv
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume coe1add.y: |- Y = ( Poly1 ` R )
  assume coe1add.b: |- B = ( Base ` Y )
  assume coe1add.p: |- .+b = ( +g ` Y )
  assume coe1add.q: |- .+ = ( +g ` R )


  assert |- ( ( ( R e. Ring /\ F e. B /\ G e. B ) /\ X e. NN0 ) -> ( ( coe1 ` ( F .+b G ) ) ` X ) = ( ( ( coe1 ` F ) ` X ) .+ ( ( coe1 ` G ) ` X ) ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    w3a
    #
    cX
    cn0
    wcel
    #
    wa
    #
    cX
    cF
    cG
    c.pb
    co
    cco1
    cfv
    #
    cfv
    cX
    cF
    cco1
    cfv
    #
    cG
    cco1
    cfv
    #
    c.pl
    cof
    co
    #
    cfv
    #
    cX
    @7
    cfv
    cX
    @8
    cfv
    c.pl
    co
    #
    @5
    cX
    @6
    @9
    @3
    @6
    @9
    wceq
    @4
    cB
    c.pl
    c.pb
    cR
    cF
    cG
    cY
    coe1add.y
    coe1add.b
    coe1add.p
    coe1add.q
    coe1add
    adantr
    fveq1d
    @5
    @7
    cn0
    wfn
    #
    @8
    cn0
    wfn
    #
    cn0
    cvv
    wcel
    #
    @4
    @10
    @11
    wceq
    @3
    @12
    @4
    @1
    @0
    @12
    @2
    @1
    cn0
    cR
    cbs
    cfv
    #
    @7
    wf
    @12
    @7
    cB
    cY
    cR
    cF
    @15
    @7
    eqid
    coe1add.b
    coe1add.y
    @15
    eqid
    #
    coe1f
    cn0
    @15
    @7
    ffn
    syl
    3ad2ant2
    adantr
    @3
    @13
    @4
    @2
    @0
    @13
    @1
    @2
    cn0
    @15
    @8
    wf
    @13
    @8
    cB
    cY
    cR
    cG
    @15
    @8
    eqid
    coe1add.b
    coe1add.y
    @16
    coe1f
    cn0
    @15
    @8
    ffn
    syl
    3ad2ant3
    adantr
    @14
    @5
    nn0ex
    a1i
    @3
    @4
    simpr
    cn0
    c.pl
    @7
    @8
    cvv
    cX
    fnfvof
    syl22anc
    eqtrd
end
