include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp23.mm"
include "simp21.mm"
include "simp22.mm"
include "simp3l.mm"
include "wi.mm"
include "lecmtN.mm"
include "syl3anc.mm"
include "mpd.mm"
include "wb.mm"
include "cmtcomN.mm"
include "mpbid.mm"
include "simp3r.mm"
include "omlfh1N.mm"
include "syl132anc.mm"
include "clat.mm"
include "omllat.mm"
include "3ad2ant1.mm"
include "latjcl.mm"
include "latmcom.mm"
include "latleeqm2.mm"
include "oveq12d.mm"
include "3eqtr3rd.mm"

theorem omlmod1i2N
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume omlmod.b: |- B = ( Base ` K )
  assume omlmod.l: |- .<_ = ( le ` K )
  assume omlmod.j: |- .\/ = ( join ` K )
  assume omlmod.m: |- ./\ = ( meet ` K )
  assume omlmod.c: |- C = ( cm ` K )


  assert |- ( ( K e. OML /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ ( X .<_ Z /\ Y C Z ) ) -> ( X .\/ ( Y ./\ Z ) ) = ( ( X .\/ Y ) ./\ Z ) )

  proof
    cK
    coml
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
    cZ
    cB
    wcel
    #
    w3a
    #
    cX
    cZ
    c.le
    wbr
    #
    cY
    cZ
    cC
    wbr
    #
    wa
    #
    w3a
    #
    cZ
    cX
    cY
    c.or
    co
    #
    c.an
    co
    #
    cZ
    cX
    c.an
    co
    #
    cZ
    cY
    c.an
    co
    #
    c.or
    co
    #
    @9
    cZ
    c.an
    co
    #
    cX
    cY
    cZ
    c.an
    co
    #
    c.or
    co
    @8
    @0
    @3
    @1
    @2
    cZ
    cX
    cC
    wbr
    #
    cZ
    cY
    cC
    wbr
    #
    @10
    @13
    wceq
    @0
    @4
    @7
    simp1
    #
    @0
    @1
    @2
    @3
    @7
    simp23
    #
    @0
    @1
    @2
    @3
    @7
    simp21
    #
    @0
    @1
    @2
    @3
    @7
    simp22
    #
    @8
    cX
    cZ
    cC
    wbr
    #
    @16
    @8
    @5
    @22
    @0
    @4
    @5
    @6
    simp3l
    #
    @8
    @0
    @1
    @3
    @5
    @22
    wi
    @18
    @20
    @19
    cB
    cC
    cK
    c.le
    cX
    cZ
    omlmod.b
    omlmod.l
    omlmod.c
    lecmtN
    syl3anc
    mpd
    @8
    @0
    @1
    @3
    @22
    @16
    wb
    @18
    @20
    @19
    cB
    cC
    cK
    cX
    cZ
    omlmod.b
    omlmod.c
    cmtcomN
    syl3anc
    mpbid
    @8
    @6
    @17
    @0
    @4
    @5
    @6
    simp3r
    @8
    @0
    @2
    @3
    @6
    @17
    wb
    @18
    @21
    @19
    cB
    cC
    cK
    cY
    cZ
    omlmod.b
    omlmod.c
    cmtcomN
    syl3anc
    mpbid
    cB
    cC
    c.or
    cK
    c.an
    cZ
    cX
    cY
    omlmod.b
    omlmod.j
    omlmod.m
    omlmod.c
    omlfh1N
    syl132anc
    @8
    cK
    clat
    wcel
    #
    @3
    @9
    cB
    wcel
    #
    @10
    @14
    wceq
    @0
    @4
    @24
    @7
    cK
    omllat
    3ad2ant1
    #
    @19
    @8
    @24
    @1
    @2
    @25
    @26
    @20
    @21
    cB
    c.or
    cK
    cX
    cY
    omlmod.b
    omlmod.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    cZ
    @9
    omlmod.b
    omlmod.m
    latmcom
    syl3anc
    @8
    @11
    cX
    @12
    @15
    c.or
    @8
    @5
    @11
    cX
    wceq
    #
    @23
    @8
    @24
    @1
    @3
    @5
    @27
    wb
    @26
    @20
    @19
    cB
    cK
    c.le
    c.an
    cX
    cZ
    omlmod.b
    omlmod.l
    omlmod.m
    latleeqm2
    syl3anc
    mpbid
    @8
    @24
    @3
    @2
    @12
    @15
    wceq
    @26
    @19
    @21
    cB
    cK
    c.an
    cZ
    cY
    omlmod.b
    omlmod.m
    latmcom
    syl3anc
    oveq12d
    3eqtr3rd
end
