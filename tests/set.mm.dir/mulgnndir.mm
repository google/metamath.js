include "csgrp.mm"
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
include "cmgm.mm"
include "sgrpmgm.mm"
include "3anim1i.mm"
include "mgmcl.mm"
include "syl.mm"
include "3expb.mm"
include "adantlr.mm"
include "wceq.mm"
include "sgrpass.mm"
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

theorem mulgnndir
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


  assert |- ( ( G e. SGrp /\ ( M e. NN /\ N e. NN /\ X e. B ) ) -> ( ( M + N ) .x. X ) = ( ( M .x. X ) .+ ( N .x. X ) ) )

  proof
    cG
    csgrp
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
    @0
    @18
    @20
    w3a
    cG
    cmgm
    wcel
    #
    @18
    @20
    w3a
    @22
    @0
    @23
    @18
    @20
    cG
    sgrpmgm
    3anim1i
    cB
    cG
    @17
    @19
    c.pl
    mulgnndir.b
    mulgnndir.p
    mgmcl
    syl
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
    @24
    c.pl
    co
    @17
    @19
    @24
    c.pl
    co
    c.pl
    co
    wceq
    @4
    cB
    cG
    @17
    @19
    c.pl
    @24
    mulgnndir.b
    mulgnndir.p
    sgrpass
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
    @25
    @27
    wcel
    @5
    cN
    cn
    @28
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
    @31
    nncnd
    #
    @5
    cN
    @29
    nncnd
    addcomd
    #
    @5
    @11
    @26
    cuz
    @5
    cM
    cc
    wcel
    c1
    cc
    wcel
    @11
    @26
    wceq
    @33
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
    @28
    @31
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
    @37
    cX
    wceq
    #
    @36
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
    @36
    @40
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
    @42
    @31
    @29
    cM
    cN
    nnaddcl
    syl2anc
    @40
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
    @31
    @40
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
    @43
    mulgnn
    syl2anc
    @5
    cN
    @8
    cfv
    #
    @25
    c.pl
    @7
    @26
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
    @30
    @32
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
    @37
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
    @38
    @39
    @46
    @40
    @17
    cN
    elfznn
    #
    @41
    syl2an
    @47
    @3
    @48
    cn
    wcel
    #
    @49
    cX
    wceq
    @5
    @3
    @46
    @40
    adantr
    @46
    @38
    @1
    @51
    @5
    @50
    @31
    @17
    cM
    nnaddcl
    syl2anr
    cn
    cX
    @48
    cB
    fvconst2g
    syl2anc
    eqtr4d
    seqshft2
    @5
    @2
    @3
    @16
    @44
    wceq
    @29
    @40
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
    @43
    mulgnn
    syl2anc
    @5
    @6
    @25
    @12
    @45
    @5
    @11
    @26
    c.pl
    @7
    @35
    seqeq1d
    @34
    fveq12d
    3eqtr4d
    oveq12d
    3eqtr4d
end
