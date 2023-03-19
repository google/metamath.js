include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "cascl.mm"
include "cif.mm"
include "cbs.mm"
include "eqid.mm"
include "ringidcl.mm"
include "ancli.mm"
include "adantl.mm"
include "ad2antrl.mm"
include "cply1coe0.mm"
include "syl.mm"
include "wb.mm"
include "iftrue.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "adantr.mm"
include "mpbird.mm"
include "wn.mm"
include "ring0cl.mm"
include "iffalse.mm"
include "pm2.61ian.mm"
include "ralrimivva.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "pmat1ovscd.mm"
include "2ralbidva.mm"
include "pmatring.mm"
include "cpmatel.mm"
include "mpd3an3.mm"

theorem 1elcpmat
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  assume cpmatsrngpmat.s: |- S = ( N ConstPolyMat R )
  assume cpmatsrngpmat.p: |- P = ( Poly1 ` R )
  assume cpmatsrngpmat.c: |- C = ( N Mat P )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( 1r ` C ) e. S )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cC
    cur
    cfv
    #
    cS
    wcel
    #
    vn
    cv
    #
    vi
    cv
    #
    vj
    cv
    #
    @3
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    vn
    cn
    wral
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @2
    @14
    @5
    @6
    @7
    wceq
    #
    cR
    cur
    cfv
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    @11
    @17
    cfv
    #
    cif
    #
    cco1
    cfv
    #
    cfv
    #
    @11
    wceq
    #
    vn
    cn
    wral
    #
    vj
    cN
    wral
    vi
    cN
    wral
    @2
    @24
    vi
    vj
    cN
    cN
    @15
    @2
    @6
    cN
    wcel
    #
    @7
    cN
    wcel
    #
    wa
    #
    wa
    #
    @24
    @15
    @28
    wa
    #
    @24
    @5
    @18
    cco1
    cfv
    #
    cfv
    #
    @11
    wceq
    #
    vn
    cn
    wral
    #
    @29
    @1
    @16
    cR
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @33
    @2
    @36
    @15
    @27
    @1
    @36
    @0
    @1
    @35
    @34
    cR
    @16
    @34
    eqid
    #
    @16
    eqid
    #
    ringidcl
    ancli
    adantl
    ad2antrl
    @17
    cP
    cbs
    cfv
    #
    cP
    cR
    @16
    vn
    @34
    @11
    @37
    @11
    eqid
    #
    cpmatsrngpmat.p
    @39
    eqid
    #
    @17
    eqid
    #
    cply1coe0
    syl
    @15
    @24
    @33
    wb
    @28
    @15
    @23
    @32
    vn
    cn
    @15
    @22
    @31
    @11
    @15
    @5
    @21
    @30
    @15
    @20
    @18
    cco1
    @15
    @18
    @19
    iftrue
    fveq2d
    fveq1d
    eqeq1d
    ralbidv
    adantr
    mpbird
    @15
    wn
    #
    @28
    wa
    #
    @24
    @5
    @19
    cco1
    cfv
    #
    cfv
    #
    @11
    wceq
    #
    vn
    cn
    wral
    #
    @2
    @48
    @43
    @27
    @2
    @1
    @11
    @34
    wcel
    #
    wa
    #
    @48
    @1
    @50
    @0
    @1
    @49
    @34
    cR
    @11
    @37
    @40
    ring0cl
    ancli
    adantl
    @17
    @39
    cP
    cR
    @11
    vn
    @34
    @11
    @37
    @40
    cpmatsrngpmat.p
    @41
    @42
    cply1coe0
    syl
    ad2antrl
    @44
    @23
    @47
    vn
    cn
    @44
    @22
    @46
    @11
    @44
    @5
    @21
    @45
    @44
    @20
    @19
    cco1
    @43
    @20
    @19
    wceq
    @28
    @15
    @18
    @19
    iffalse
    adantr
    fveq2d
    fveq1d
    eqeq1d
    ralbidv
    mpbird
    pm2.61ian
    ralrimivva
    @2
    @13
    @24
    vi
    vj
    cN
    cN
    @28
    @12
    @23
    vn
    cn
    @28
    @10
    @22
    @11
    @28
    @5
    @9
    @21
    @28
    @8
    @20
    cco1
    @28
    @17
    cC
    cP
    cR
    @3
    @16
    @6
    @7
    cN
    @11
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @42
    @40
    @38
    @0
    @1
    @27
    simpll
    @0
    @1
    @27
    simplr
    @2
    @25
    @26
    simprl
    @2
    @25
    @26
    simprr
    @3
    eqid
    #
    pmat1ovscd
    fveq2d
    fveq1d
    eqeq1d
    ralbidv
    2ralbidva
    mpbird
    @0
    @1
    @3
    cC
    cbs
    cfv
    #
    wcel
    #
    @4
    @14
    wb
    @2
    cC
    crg
    wcel
    @53
    cC
    cP
    cR
    cN
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    pmatring
    @52
    cC
    @3
    @52
    eqid
    #
    @51
    ringidcl
    syl
    @52
    cC
    cP
    cR
    cS
    vi
    vj
    vn
    @3
    cN
    crg
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @54
    cpmatel
    mpd3an3
    mpbird
end
