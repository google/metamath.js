include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "coc.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "eqid.mm"
include "cmt4N.mm"
include "3adant3r3.mm"
include "3adant3r2.mm"
include "anbi12d.mm"
include "wi.mm"
include "simpl.mm"
include "cops.mm"
include "omlop.mm"
include "adantr.mm"
include "simpr1.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "simpr2.mm"
include "simpr3.mm"
include "3jca.mm"
include "omlfh1N.mm"
include "fveq2d.mm"
include "3exp.mm"
include "sylc.mm"
include "sylbid.mm"
include "3impia.mm"
include "col.mm"
include "omlol.mm"
include "clat.mm"
include "omllat.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "oldmm2.mm"
include "oldmj4.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "3adant3.mm"
include "latmcl.mm"
include "oldmj1.mm"
include "oldmm4.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem omlfh3N
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume omlfh1.b: |- B = ( Base ` K )
  assume omlfh1.j: |- .\/ = ( join ` K )
  assume omlfh1.m: |- ./\ = ( meet ` K )
  assume omlfh1.c: |- C = ( cm ` K )


  assert |- ( ( K e. OML /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ ( X C Y /\ X C Z ) ) -> ( X .\/ ( Y ./\ Z ) ) = ( ( X .\/ Y ) ./\ ( X .\/ Z ) ) )

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
    cY
    cC
    wbr
    #
    cX
    cZ
    cC
    wbr
    #
    wa
    #
    w3a
    cX
    cK
    coc
    cfv
    #
    cfv
    #
    cY
    @8
    cfv
    #
    cZ
    @8
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    @8
    cfv
    #
    @9
    @10
    c.an
    co
    #
    @9
    @11
    c.an
    co
    #
    c.or
    co
    #
    @8
    cfv
    #
    cX
    cY
    cZ
    c.an
    co
    #
    c.or
    co
    #
    cX
    cY
    c.or
    co
    #
    cX
    cZ
    c.or
    co
    #
    c.an
    co
    #
    @0
    @4
    @7
    @14
    @18
    wceq
    #
    @0
    @4
    wa
    #
    @7
    @9
    @10
    cC
    wbr
    #
    @9
    @11
    cC
    wbr
    #
    wa
    #
    @24
    @25
    @5
    @26
    @6
    @27
    @0
    @1
    @2
    @5
    @26
    wb
    @3
    cB
    cC
    cK
    @8
    cX
    cY
    omlfh1.b
    @8
    eqid
    #
    omlfh1.c
    cmt4N
    3adant3r3
    @0
    @1
    @3
    @6
    @27
    wb
    @2
    cB
    cC
    cK
    @8
    cX
    cZ
    omlfh1.b
    @29
    omlfh1.c
    cmt4N
    3adant3r2
    anbi12d
    @25
    @0
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    w3a
    #
    @28
    @24
    wi
    @0
    @4
    simpl
    @25
    @30
    @31
    @32
    @25
    cK
    cops
    wcel
    #
    @1
    @30
    @0
    @34
    @4
    cK
    omlop
    adantr
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    cB
    cK
    @8
    cX
    omlfh1.b
    @29
    opoccl
    syl2anc
    #
    @25
    @34
    @2
    @31
    @35
    @0
    @1
    @2
    @3
    simpr2
    #
    cB
    cK
    @8
    cY
    omlfh1.b
    @29
    opoccl
    syl2anc
    #
    @25
    @34
    @3
    @32
    @35
    @0
    @1
    @2
    @3
    simpr3
    #
    cB
    cK
    @8
    cZ
    omlfh1.b
    @29
    opoccl
    syl2anc
    #
    3jca
    @0
    @33
    @28
    @24
    @0
    @33
    @28
    w3a
    @13
    @17
    @8
    cB
    cC
    c.or
    cK
    c.an
    @9
    @10
    @11
    omlfh1.b
    omlfh1.j
    omlfh1.m
    omlfh1.c
    omlfh1N
    fveq2d
    3exp
    sylc
    sylbid
    3impia
    @0
    @4
    @20
    @14
    wceq
    @7
    @25
    @14
    cX
    @12
    @8
    cfv
    #
    c.or
    co
    #
    @20
    @25
    cK
    col
    wcel
    #
    @1
    @12
    cB
    wcel
    #
    @14
    @43
    wceq
    @0
    @44
    @4
    cK
    omlol
    adantr
    #
    @36
    @25
    cK
    clat
    wcel
    #
    @31
    @32
    @45
    @0
    @47
    @4
    cK
    omllat
    adantr
    #
    @39
    @41
    cB
    c.or
    cK
    @10
    @11
    omlfh1.b
    omlfh1.j
    latjcl
    syl3anc
    cB
    c.or
    cK
    c.an
    @8
    cX
    @12
    omlfh1.b
    omlfh1.j
    omlfh1.m
    @29
    oldmm2
    syl3anc
    @25
    @42
    @19
    cX
    c.or
    @25
    @44
    @2
    @3
    @42
    @19
    wceq
    @46
    @38
    @40
    cB
    c.or
    cK
    c.an
    @8
    cY
    cZ
    omlfh1.b
    omlfh1.j
    omlfh1.m
    @29
    oldmj4
    syl3anc
    oveq2d
    eqtr2d
    3adant3
    @0
    @4
    @23
    @18
    wceq
    @7
    @25
    @18
    @15
    @8
    cfv
    #
    @16
    @8
    cfv
    #
    c.an
    co
    #
    @23
    @25
    @44
    @15
    cB
    wcel
    #
    @16
    cB
    wcel
    #
    @18
    @51
    wceq
    @46
    @25
    @47
    @30
    @31
    @52
    @48
    @37
    @39
    cB
    cK
    c.an
    @9
    @10
    omlfh1.b
    omlfh1.m
    latmcl
    syl3anc
    @25
    @47
    @30
    @32
    @53
    @48
    @37
    @41
    cB
    cK
    c.an
    @9
    @11
    omlfh1.b
    omlfh1.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    c.an
    @8
    @15
    @16
    omlfh1.b
    omlfh1.j
    omlfh1.m
    @29
    oldmj1
    syl3anc
    @25
    @49
    @21
    @50
    @22
    c.an
    @25
    @44
    @1
    @2
    @49
    @21
    wceq
    @46
    @36
    @38
    cB
    c.or
    cK
    c.an
    @8
    cX
    cY
    omlfh1.b
    omlfh1.j
    omlfh1.m
    @29
    oldmm4
    syl3anc
    @25
    @44
    @1
    @3
    @50
    @22
    wceq
    @46
    @36
    @40
    cB
    c.or
    cK
    c.an
    @8
    cX
    cZ
    omlfh1.b
    omlfh1.j
    omlfh1.m
    @29
    oldmm4
    syl3anc
    oveq12d
    eqtr2d
    3adant3
    3eqtr4d
end
