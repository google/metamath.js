include "cmnd.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cv.mm"
include "mndcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "wceq.mm"
include "mndass.mm"
include "cuz.mm"
include "cz.mm"
include "simpr2.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "simpr1.mm"
include "nnzd.mm"
include "eluzadd.mm"
include "syl2anc.mm"
include "nncnd.mm"
include "addcomd.mm"
include "cc.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "3eltr4d.mm"
include "cfz.mm"
include "simpr3.mm"
include "elfznn.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "seqsplit.mm"
include "nnaddcl.mm"
include "eqid.mm"
include "mulgnn.mm"
include "syl2anr.mm"
include "eqtr4d.mm"
include "seqshft2.mm"
include "seqeq1d.mm"
include "fveq12d.mm"
include "3eqtr4d.mm"
include "oveq12d.mm"

theorem mulgnndirOLD
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mulgnndir.b: |- B = ( Base ` G )
  assume mulgnndir.t: |- .x. = ( .g ` G )
  assume mulgnndir.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Mnd /\ ( M e. NN /\ N e. NN /\ X e. B ) ) -> ( ( M + N ) .x. X ) = ( ( M .x. X ) .+ ( N .x. X ) ) )

  proof
    cG
    cmnd
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cM
    cN
    caddc
    co
    #
    c.pl
    cn
    cX
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    cM
    @8
    cfv
    #
    @6
    c.pl
    @7
    cM
    c1
    caddc
    co
    #
    cseq
    #
    cfv
    #
    c.pl
    co
    @6
    cX
    c.x
    co
    #
    cM
    cX
    c.x
    co
    #
    cN
    cX
    c.x
    co
    #
    c.pl
    co
    @5
    vx
    vy
    vz
    c.pl
    cB
    @7
    c1
    cM
    @6
    @0
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    @17
    @19
    c.pl
    co
    #
    cB
    wcel
    #
    @4
    @0
    @18
    @20
    @22
    cB
    c.pl
    cG
    @17
    @19
    mulgnndir.b
    mulgnndir.p
    mndcl
    3expb
    adantlr
    @0
    @18
    @20
    vz
    cv
    #
    cB
    wcel
    w3a
    @21
    @23
    c.pl
    co
    @17
    @19
    @23
    c.pl
    co
    c.pl
    co
    wceq
    @4
    cB
    c.pl
    cG
    @17
    @19
    @23
    mulgnndir.b
    mulgnndir.p
    mndass
    adantlr
    @5
    cN
    cM
    caddc
    co
    #
    c1
    cM
    caddc
    co
    #
    cuz
    cfv
    #
    @6
    @11
    cuz
    cfv
    @5
    cN
    c1
    cuz
    cfv
    #
    wcel
    cM
    cz
    wcel
    @24
    @26
    wcel
    @5
    cN
    cn
    @27
    @0
    @1
    @2
    @3
    simpr2
    #
    nnuz
    syl6eleq
    #
    @5
    cM
    @0
    @1
    @2
    @3
    simpr1
    #
    nnzd
    #
    cM
    c1
    cN
    eluzadd
    syl2anc
    @5
    cM
    cN
    @5
    cM
    @30
    nncnd
    #
    @5
    cN
    @28
    nncnd
    addcomd
    #
    @5
    @11
    @25
    cuz
    @5
    cM
    cc
    wcel
    c1
    cc
    wcel
    @11
    @25
    wceq
    @32
    ax-1cn
    cM
    c1
    addcom
    sylancl
    #
    fveq2d
    3eltr4d
    @5
    cM
    cn
    @27
    @30
    nnuz
    syl6eleq
    @5
    @17
    c1
    @6
    cfz
    co
    wcel
    #
    wa
    @17
    @7
    cfv
    #
    cX
    cB
    @5
    @3
    @17
    cn
    wcel
    #
    @36
    cX
    wceq
    #
    @35
    @0
    @1
    @2
    @3
    simpr3
    #
    @17
    @6
    elfznn
    cn
    cX
    @17
    cB
    fvconst2g
    #
    syl2an
    @5
    @3
    @35
    @39
    adantr
    eqeltrd
    seqsplit
    @5
    @6
    cn
    wcel
    #
    @3
    @14
    @9
    wceq
    @5
    @1
    @2
    @41
    @30
    @28
    cM
    cN
    nnaddcl
    syl2anc
    @39
    cB
    c.pl
    @8
    c.x
    cG
    @6
    cX
    mulgnndir.b
    mulgnndir.p
    mulgnndir.t
    @8
    eqid
    #
    mulgnn
    syl2anc
    @5
    @15
    @10
    @16
    @13
    c.pl
    @5
    @1
    @3
    @15
    @10
    wceq
    @30
    @39
    cB
    c.pl
    @8
    c.x
    cG
    cM
    cX
    mulgnndir.b
    mulgnndir.p
    mulgnndir.t
    @42
    mulgnn
    syl2anc
    @5
    cN
    @8
    cfv
    #
    @24
    c.pl
    @7
    @25
    cseq
    #
    cfv
    @16
    @13
    @5
    c.pl
    vx
    @7
    @7
    cM
    c1
    cN
    @29
    @31
    @5
    @17
    c1
    cN
    cfz
    co
    wcel
    #
    wa
    #
    @36
    cX
    @17
    cM
    caddc
    co
    #
    @7
    cfv
    #
    @5
    @3
    @37
    @38
    @45
    @39
    @17
    cN
    elfznn
    #
    @40
    syl2an
    @46
    @3
    @47
    cn
    wcel
    #
    @48
    cX
    wceq
    @5
    @3
    @45
    @39
    adantr
    @45
    @37
    @1
    @50
    @5
    @49
    @30
    @17
    cM
    nnaddcl
    syl2anr
    cn
    cX
    @47
    cB
    fvconst2g
    syl2anc
    eqtr4d
    seqshft2
    @5
    @2
    @3
    @16
    @43
    wceq
    @28
    @39
    cB
    c.pl
    @8
    c.x
    cG
    cN
    cX
    mulgnndir.b
    mulgnndir.p
    mulgnndir.t
    @42
    mulgnn
    syl2anc
    @5
    @6
    @24
    @12
    @44
    @5
    @11
    @25
    c.pl
    @7
    @34
    seqeq1d
    @33
    fveq12d
    3eqtr4d
    oveq12d
    3eqtr4d
end
