include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "eqid.mm"
include "coe1ae0.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "caddc.mm"
include "co.mm"
include "nn0addcl.mm"
include "adantr.mm"
include "wb.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "adantl.mm"
include "r19.26.mm"
include "cc.mm"
include "nn0cn.mm"
include "addcomd.mm"
include "3adant3.mm"
include "breq1d.mm"
include "nn0sumltlt.mm"
include "sylbid.mm"
include "3expia.mm"
include "ancoms.mm"
include "imp.mm"
include "imim1d.mm"
include "com23.mm"
include "anim12d.mm"
include "ancomd.mm"
include "exp31.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "rspcedvd.mm"
include "expd.mm"
include "com34.mm"
include "impancom.mm"
include "com14.mm"
include "impcom.mm"
include "rexlimiva.mm"
include "com13.mm"
include "mpcom.mm"
include "mpd.mm"

theorem ply1mulgsumlem1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vn: setvar n
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x
  assume ply1mulgsum.p: |- P = ( Poly1 ` R )
  assume ply1mulgsum.b: |- B = ( Base ` P )
  assume ply1mulgsum.a: |- A = ( coe1 ` K )
  assume ply1mulgsum.c: |- C = ( coe1 ` L )
  assume ply1mulgsum.x: |- X = ( var1 ` R )
  assume ply1mulgsum.pm: |- .X. = ( .r ` P )
  assume ply1mulgsum.sm: |- .x. = ( .s ` P )
  assume ply1mulgsum.rm: |- .* = ( .r ` R )
  assume ply1mulgsum.m: |- M = ( mulGrp ` P )
  assume ply1mulgsum.e: |- .^ = ( .g ` M )

  disjoint A n
  disjoint A s
  disjoint n s
  disjoint B n
  disjoint B s
  disjoint C n
  disjoint C s
  disjoint K n
  disjoint K s
  disjoint L n
  disjoint L s
  disjoint R n
  disjoint R s
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a n
  disjoint a s
  disjoint b n
  disjoint b s
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint K a
  disjoint K b
  disjoint L a
  disjoint L b
  disjoint R a
  disjoint R b
  disjoint k x
  assert |- ( ( R e. Ring /\ K e. B /\ L e. B ) -> E. s e. NN0 A. n e. NN0 ( s < n -> ( ( A ` n ) = ( 0g ` R ) /\ ( C ` n ) = ( 0g ` R ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cK
    cB
    wcel
    #
    cL
    cB
    wcel
    #
    w3a
    #
    vb
    cv
    #
    vn
    cv
    #
    clt
    wbr
    #
    @5
    cA
    cfv
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    #
    vb
    cn0
    wrex
    #
    vs
    cv
    #
    @5
    clt
    wbr
    #
    @8
    @5
    cC
    cfv
    @7
    wceq
    #
    wa
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    @1
    @0
    @11
    @2
    cA
    cB
    cP
    cR
    vn
    cK
    @7
    vb
    ply1mulgsum.a
    ply1mulgsum.b
    ply1mulgsum.p
    @7
    eqid
    #
    coe1ae0
    3ad2ant2
    va
    cv
    #
    @5
    clt
    wbr
    #
    @14
    wi
    #
    vn
    cn0
    wral
    #
    va
    cn0
    wrex
    #
    @3
    @11
    @18
    wi
    #
    @2
    @0
    @24
    @1
    cC
    cB
    cP
    cR
    vn
    cL
    @7
    va
    ply1mulgsum.c
    ply1mulgsum.b
    ply1mulgsum.p
    @19
    coe1ae0
    3ad2ant3
    @23
    @3
    @25
    wi
    va
    cn0
    @11
    @3
    @20
    cn0
    wcel
    #
    @23
    wa
    #
    @18
    @10
    @3
    @27
    @18
    wi
    wi
    #
    vb
    cn0
    @10
    @4
    cn0
    wcel
    #
    @28
    @27
    @29
    @3
    @10
    @18
    @26
    @29
    @23
    @3
    @10
    @18
    wi
    wi
    @26
    @29
    wa
    #
    @23
    @10
    @3
    @18
    @30
    @23
    @10
    @3
    @18
    wi
    @30
    @3
    @23
    @10
    wa
    #
    @18
    @30
    @3
    @31
    @18
    @30
    @3
    wa
    #
    @31
    wa
    #
    @17
    @20
    @4
    caddc
    co
    #
    @5
    clt
    wbr
    #
    @15
    wi
    #
    vn
    cn0
    wral
    #
    vs
    @34
    cn0
    @32
    @34
    cn0
    wcel
    #
    @31
    @30
    @38
    @3
    @20
    @4
    nn0addcl
    adantr
    adantr
    @12
    @34
    wceq
    #
    @17
    @37
    wb
    @33
    @39
    @16
    @36
    vn
    cn0
    @39
    @13
    @35
    @15
    @12
    @34
    @5
    clt
    breq1
    imbi1d
    ralbidv
    adantl
    @32
    @31
    @37
    @31
    @22
    @9
    wa
    #
    vn
    cn0
    wral
    @32
    @37
    @22
    @9
    vn
    cn0
    r19.26
    @32
    @40
    @36
    vn
    cn0
    @32
    @5
    cn0
    wcel
    #
    wa
    #
    @35
    @40
    @15
    @42
    @35
    @40
    @15
    @42
    @35
    wa
    #
    @40
    wa
    @14
    @8
    @43
    @40
    @14
    @8
    wa
    @43
    @22
    @14
    @9
    @8
    @42
    @35
    @22
    @14
    wi
    @42
    @22
    @35
    @14
    @42
    @35
    @21
    @14
    @32
    @41
    @35
    @21
    wi
    #
    @30
    @41
    @44
    wi
    #
    @3
    @29
    @26
    @45
    @29
    @26
    @41
    @44
    @29
    @26
    @41
    w3a
    #
    @35
    @4
    @20
    caddc
    co
    #
    @5
    clt
    wbr
    @21
    @46
    @34
    @47
    @5
    clt
    @29
    @26
    @34
    @47
    wceq
    @41
    @29
    @26
    wa
    @20
    @4
    @26
    @20
    cc
    wcel
    @29
    @20
    nn0cn
    adantl
    @29
    @4
    cc
    wcel
    @26
    @4
    nn0cn
    adantr
    addcomd
    3adant3
    breq1d
    vb
    va
    vn
    nn0sumltlt
    sylbid
    3expia
    ancoms
    adantr
    imp
    imim1d
    com23
    imp
    @42
    @35
    @9
    @8
    wi
    @42
    @9
    @35
    @8
    @42
    @35
    @6
    @8
    @32
    @41
    @35
    @6
    wi
    #
    @30
    @41
    @48
    wi
    @3
    @26
    @29
    @41
    @48
    va
    vb
    vn
    nn0sumltlt
    3expia
    adantr
    imp
    imim1d
    com23
    imp
    anim12d
    imp
    ancomd
    exp31
    com23
    ralimdva
    syl5bir
    imp
    rspcedvd
    exp31
    com23
    expd
    com34
    impancom
    com14
    impcom
    rexlimiva
    com13
    rexlimiva
    mpcom
    mpd
end
