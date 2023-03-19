include "cabl.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cgrp.mm"
include "wb.mm"
include "ablgrp.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "simp3l.mm"
include "simp3r.mm"
include "grpsubrcan.mm"
include "syl13anc.mm"
include "c0g.mm"
include "cfv.mm"
include "simp1.mm"
include "ablsub4.mm"
include "syl122anc.mm"
include "eqid.mm"
include "grpsubid.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "grpsubcl.mm"
include "grprid.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "grplid.mm"
include "eqeq12d.mm"
include "bitr3d.mm"

theorem abladdsub4
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


  assert |- ( ( G e. Abel /\ ( X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B ) ) -> ( ( X .+ Y ) = ( Z .+ W ) <-> ( X .- Z ) = ( W .- Y ) ) )

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
    cY
    c.pl
    co
    #
    c.mi
    co
    #
    cZ
    cW
    c.pl
    co
    #
    @9
    c.mi
    co
    #
    wceq
    #
    @8
    @11
    wceq
    #
    cX
    cZ
    c.mi
    co
    #
    cW
    cY
    c.mi
    co
    #
    wceq
    @7
    cG
    cgrp
    wcel
    #
    @8
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    @13
    @14
    wb
    @0
    @3
    @17
    @6
    cG
    ablgrp
    3ad2ant1
    #
    @7
    @17
    @1
    @2
    @18
    @21
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
    @17
    @4
    @5
    @19
    @21
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
    @7
    @17
    @4
    @2
    @20
    @21
    @24
    @23
    cB
    c.pl
    cG
    cZ
    cY
    ablsubadd.b
    ablsubadd.p
    grpcl
    syl3anc
    cB
    cG
    c.mi
    @8
    @11
    @9
    ablsubadd.b
    ablsubadd.m
    grpsubrcan
    syl13anc
    @7
    @10
    @15
    @12
    @16
    @7
    @10
    @15
    cY
    cY
    c.mi
    co
    #
    c.pl
    co
    #
    @15
    cG
    c0g
    cfv
    #
    c.pl
    co
    #
    @15
    @7
    @0
    @1
    @2
    @4
    @2
    @10
    @27
    wceq
    @0
    @3
    @6
    simp1
    #
    @22
    @23
    @24
    @23
    cB
    c.pl
    cG
    c.mi
    cY
    cX
    cY
    cZ
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    ablsub4
    syl122anc
    @7
    @26
    @28
    @15
    c.pl
    @7
    @17
    @2
    @26
    @28
    wceq
    @21
    @23
    cB
    cG
    c.mi
    cY
    @28
    ablsubadd.b
    @28
    eqid
    #
    ablsubadd.m
    grpsubid
    syl2anc
    oveq2d
    @7
    @17
    @15
    cB
    wcel
    #
    @29
    @15
    wceq
    @21
    @7
    @17
    @1
    @4
    @32
    @21
    @22
    @24
    cB
    cG
    c.mi
    cX
    cZ
    ablsubadd.b
    ablsubadd.m
    grpsubcl
    syl3anc
    cB
    c.pl
    cG
    @15
    @28
    ablsubadd.b
    ablsubadd.p
    @31
    grprid
    syl2anc
    3eqtrd
    @7
    @12
    cZ
    cZ
    c.mi
    co
    #
    @16
    c.pl
    co
    #
    @28
    @16
    c.pl
    co
    #
    @16
    @7
    @0
    @4
    @5
    @4
    @2
    @12
    @34
    wceq
    @30
    @24
    @25
    @24
    @23
    cB
    c.pl
    cG
    c.mi
    cY
    cZ
    cW
    cZ
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    ablsub4
    syl122anc
    @7
    @33
    @28
    @16
    c.pl
    @7
    @17
    @4
    @33
    @28
    wceq
    @21
    @24
    cB
    cG
    c.mi
    cZ
    @28
    ablsubadd.b
    @31
    ablsubadd.m
    grpsubid
    syl2anc
    oveq1d
    @7
    @17
    @16
    cB
    wcel
    #
    @35
    @16
    wceq
    @21
    @7
    @17
    @5
    @2
    @36
    @21
    @25
    @23
    cB
    cG
    c.mi
    cW
    cY
    ablsubadd.b
    ablsubadd.m
    grpsubcl
    syl3anc
    cB
    c.pl
    cG
    @16
    @28
    ablsubadd.b
    ablsubadd.p
    @31
    grplid
    syl2anc
    3eqtrd
    eqeq12d
    bitr3d
end
