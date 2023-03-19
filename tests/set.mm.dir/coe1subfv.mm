include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cn0.mm"
include "wa.mm"
include "cco1.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cplusg.mm"
include "simpl1.mm"
include "cgrp.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "syl.mm"
include "grpsubcl.mm"
include "syl3an1.mm"
include "adantr.mm"
include "simpl3.mm"
include "simpr.mm"
include "eqid.mm"
include "coe1addfv.mm"
include "syl31anc.mm"
include "3ad2ant1.mm"
include "simpl2.mm"
include "grpnpcan.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "cbs.mm"
include "wb.mm"
include "wf.mm"
include "coe1f.mm"
include "3ad2ant2.mm"
include "ffvelrnda.mm"
include "3ad2ant3.mm"
include "grpsubadd.mm"
include "syl13anc.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem coe1subfv
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  assume coe1sub.y: |- Y = ( Poly1 ` R )
  assume coe1sub.b: |- B = ( Base ` Y )
  assume coe1sub.p: |- .- = ( -g ` Y )
  assume coe1sub.q: |- N = ( -g ` R )


  assert |- ( ( ( R e. Ring /\ F e. B /\ G e. B ) /\ X e. NN0 ) -> ( ( coe1 ` ( F .- G ) ) ` X ) = ( ( ( coe1 ` F ) ` X ) N ( ( coe1 ` G ) ` X ) ) )

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
    cco1
    cfv
    #
    cfv
    #
    cX
    cG
    cco1
    cfv
    #
    cfv
    #
    cN
    co
    #
    cX
    cF
    cG
    c.mi
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @5
    @10
    @13
    wceq
    #
    @13
    @9
    cR
    cplusg
    cfv
    #
    co
    #
    @7
    wceq
    #
    @5
    cX
    @11
    cG
    cY
    cplusg
    cfv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @16
    @7
    @5
    @0
    @11
    cB
    wcel
    #
    @2
    @4
    @21
    @16
    wceq
    @0
    @1
    @2
    @4
    simpl1
    @3
    @22
    @4
    @0
    cY
    cgrp
    wcel
    #
    @1
    @2
    @22
    @0
    cY
    crg
    wcel
    @23
    cY
    cR
    coe1sub.y
    ply1ring
    cY
    ringgrp
    syl
    #
    cB
    cY
    c.mi
    cF
    cG
    coe1sub.b
    coe1sub.p
    grpsubcl
    syl3an1
    #
    adantr
    @0
    @1
    @2
    @4
    simpl3
    #
    @3
    @4
    simpr
    cB
    @15
    @18
    cR
    @11
    cG
    cX
    cY
    coe1sub.y
    coe1sub.b
    @18
    eqid
    #
    @15
    eqid
    #
    coe1addfv
    syl31anc
    @5
    cX
    @20
    @6
    @5
    @19
    cF
    cco1
    @5
    @23
    @1
    @2
    @19
    cF
    wceq
    @3
    @23
    @4
    @0
    @1
    @23
    @2
    @24
    3ad2ant1
    adantr
    @0
    @1
    @2
    @4
    simpl2
    @26
    cB
    @18
    cY
    c.mi
    cF
    cG
    coe1sub.b
    @27
    coe1sub.p
    grpnpcan
    syl3anc
    fveq2d
    fveq1d
    eqtr3d
    @5
    cR
    cgrp
    wcel
    #
    @7
    cR
    cbs
    cfv
    #
    wcel
    @9
    @30
    wcel
    @13
    @30
    wcel
    @14
    @17
    wb
    @3
    @29
    @4
    @0
    @1
    @29
    @2
    cR
    ringgrp
    3ad2ant1
    adantr
    @3
    cn0
    @30
    cX
    @6
    @1
    @0
    cn0
    @30
    @6
    wf
    @2
    @6
    cB
    cY
    cR
    cF
    @30
    @6
    eqid
    coe1sub.b
    coe1sub.y
    @30
    eqid
    #
    coe1f
    3ad2ant2
    ffvelrnda
    @3
    cn0
    @30
    cX
    @8
    @2
    @0
    cn0
    @30
    @8
    wf
    @1
    @8
    cB
    cY
    cR
    cG
    @30
    @8
    eqid
    coe1sub.b
    coe1sub.y
    @31
    coe1f
    3ad2ant3
    ffvelrnda
    @3
    cn0
    @30
    cX
    @12
    @3
    @22
    cn0
    @30
    @12
    wf
    @25
    @12
    cB
    cY
    cR
    @11
    @30
    @12
    eqid
    coe1sub.b
    coe1sub.y
    @31
    coe1f
    syl
    ffvelrnda
    @30
    @15
    cR
    cN
    @7
    @9
    @13
    @31
    @28
    coe1sub.q
    grpsubadd
    syl13anc
    mpbird
    eqcomd
end
