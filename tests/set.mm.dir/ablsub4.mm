include "cabl.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "wceq.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "simp3l.mm"
include "simp3r.mm"
include "eqid.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "ccmn.mm"
include "ablcmn.mm"
include "simp2.mm"
include "grpinvcl.mm"
include "cmn4.mm"
include "syl112anc.mm"
include "simp1.mm"
include "ablinvadd.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"

theorem ablsub4
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ablsubadd.b: |- B = ( Base ` G )
  assume ablsubadd.p: |- .+ = ( +g ` G )
  assume ablsubadd.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Abel /\ ( X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B ) ) -> ( ( X .+ Y ) .- ( Z .+ W ) ) = ( ( X .- Z ) .+ ( Y .- W ) ) )

  proof
    cG
    cabl
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cZ
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.pl
    co
    #
    cZ
    cW
    c.pl
    co
    #
    c.mi
    co
    #
    @8
    @9
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    cX
    cZ
    c.mi
    co
    #
    cY
    cW
    c.mi
    co
    #
    c.pl
    co
    #
    @7
    @8
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    @10
    @13
    wceq
    @7
    cG
    cgrp
    wcel
    #
    @1
    @2
    @17
    @0
    @3
    @19
    @6
    cG
    ablgrp
    3ad2ant1
    #
    @0
    @1
    @2
    @6
    simp2l
    #
    @0
    @1
    @2
    @6
    simp2r
    #
    cB
    c.pl
    cG
    cX
    cY
    ablsubadd.b
    ablsubadd.p
    grpcl
    syl3anc
    @7
    @19
    @4
    @5
    @18
    @20
    @0
    @3
    @4
    @5
    simp3l
    #
    @0
    @3
    @4
    @5
    simp3r
    #
    cB
    c.pl
    cG
    cZ
    cW
    ablsubadd.b
    ablsubadd.p
    grpcl
    syl3anc
    cB
    c.pl
    cG
    @11
    c.mi
    @8
    @9
    ablsubadd.b
    ablsubadd.p
    @11
    eqid
    #
    ablsubadd.m
    grpsubval
    syl2anc
    @7
    @8
    cZ
    @11
    cfv
    #
    cW
    @11
    cfv
    #
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    @26
    c.pl
    co
    #
    cY
    @27
    c.pl
    co
    #
    c.pl
    co
    #
    @13
    @16
    @7
    cG
    ccmn
    wcel
    #
    @3
    @26
    cB
    wcel
    #
    @27
    cB
    wcel
    #
    @29
    @32
    wceq
    @0
    @3
    @33
    @6
    cG
    ablcmn
    3ad2ant1
    @0
    @3
    @6
    simp2
    @7
    @19
    @4
    @34
    @20
    @23
    cB
    cG
    @11
    cZ
    ablsubadd.b
    @25
    grpinvcl
    syl2anc
    @7
    @19
    @5
    @35
    @20
    @24
    cB
    cG
    @11
    cW
    ablsubadd.b
    @25
    grpinvcl
    syl2anc
    cB
    c.pl
    cG
    @27
    cX
    cY
    @26
    ablsubadd.b
    ablsubadd.p
    cmn4
    syl112anc
    @7
    @12
    @28
    @8
    c.pl
    @7
    @0
    @4
    @5
    @12
    @28
    wceq
    @0
    @3
    @6
    simp1
    @23
    @24
    cB
    c.pl
    cG
    @11
    cZ
    cW
    ablsubadd.b
    ablsubadd.p
    @25
    ablinvadd
    syl3anc
    oveq2d
    @7
    @14
    @30
    @15
    @31
    c.pl
    @7
    @1
    @4
    @14
    @30
    wceq
    @21
    @23
    cB
    c.pl
    cG
    @11
    c.mi
    cX
    cZ
    ablsubadd.b
    ablsubadd.p
    @25
    ablsubadd.m
    grpsubval
    syl2anc
    @7
    @2
    @5
    @15
    @31
    wceq
    @22
    @24
    cB
    c.pl
    cG
    @11
    c.mi
    cY
    cW
    ablsubadd.b
    ablsubadd.p
    @25
    ablsubadd.m
    grpsubval
    syl2anc
    oveq12d
    3eqtr4d
    eqtrd
end
