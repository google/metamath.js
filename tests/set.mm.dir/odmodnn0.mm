include "cmnd.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cfv.mm"
include "cn.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cmul.mm"
include "cmo.mm"
include "caddc.mm"
include "cplusg.mm"
include "wceq.mm"
include "simpl1.mm"
include "nnnn0.mm"
include "adantl.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "simpl3.mm"
include "nn0red.mm"
include "crp.mm"
include "nnrp.mm"
include "rerpdivcld.mm"
include "clt.mm"
include "nn0ge0d.mm"
include "nnre.mm"
include "nngt0.mm"
include "divge0.mm"
include "syl22anc.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0mulcld.mm"
include "cz.mm"
include "nn0zd.mm"
include "zmodcl.mm"
include "sylancom.mm"
include "simpl2.mm"
include "eqid.mm"
include "mulgnn0dir.mm"
include "syl13anc.mm"
include "recnd.mm"
include "nn0cnd.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "mulgnn0ass.mm"
include "odid.mm"
include "syl.mm"
include "oveq2d.mm"
include "mulgnn0z.mm"
include "eqtrd.mm"
include "cmin.mm"
include "modval.mm"
include "pncan3d.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "mndlid.mm"
include "3eqtr3rd.mm"

theorem odmodnn0
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )


  assert |- ( ( ( G e. Mnd /\ A e. X /\ N e. NN0 ) /\ ( O ` A ) e. NN ) -> ( ( N mod ( O ` A ) ) .x. A ) = ( N .x. A ) )

  proof
    cG
    cmnd
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    cO
    cfv
    #
    cn
    wcel
    #
    wa
    #
    @4
    cN
    @4
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cN
    @4
    cmo
    co
    #
    caddc
    co
    #
    cA
    c.x
    co
    #
    c.0
    @10
    cA
    c.x
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cN
    cA
    c.x
    co
    @13
    @6
    @12
    @9
    cA
    c.x
    co
    #
    @13
    @14
    co
    #
    @15
    @6
    @0
    @9
    cn0
    wcel
    @10
    cn0
    wcel
    #
    @1
    @12
    @17
    wceq
    @0
    @1
    @2
    @5
    simpl1
    #
    @6
    @4
    @8
    @5
    @4
    cn0
    wcel
    #
    @3
    @4
    nnnn0
    adantl
    #
    @6
    @7
    cr
    wcel
    cc0
    @7
    cle
    wbr
    #
    @8
    cn0
    wcel
    #
    @6
    cN
    @4
    @6
    cN
    @0
    @1
    @2
    @5
    simpl3
    #
    nn0red
    #
    @5
    @4
    crp
    wcel
    #
    @3
    @4
    nnrp
    adantl
    #
    rerpdivcld
    @6
    cN
    cr
    wcel
    #
    cc0
    cN
    cle
    wbr
    @4
    cr
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    @22
    @25
    @6
    cN
    @24
    nn0ge0d
    @5
    @29
    @3
    @4
    nnre
    adantl
    #
    @5
    @30
    @3
    @4
    nngt0
    adantl
    cN
    @4
    divge0
    syl22anc
    @7
    flge0nn0
    syl2anc
    #
    nn0mulcld
    #
    @3
    @5
    cN
    cz
    wcel
    @18
    @6
    cN
    @24
    nn0zd
    cN
    @4
    zmodcl
    sylancom
    #
    @0
    @1
    @2
    @5
    simpl2
    #
    cX
    @14
    c.x
    cG
    @9
    @10
    cA
    odcl.1
    odid.3
    @14
    eqid
    #
    mulgnn0dir
    syl13anc
    @6
    @16
    c.0
    @13
    @14
    @6
    @16
    @8
    @4
    cmul
    co
    #
    cA
    c.x
    co
    #
    c.0
    @6
    @9
    @37
    cA
    c.x
    @6
    @4
    @8
    @6
    @4
    @31
    recnd
    @6
    @8
    @32
    nn0cnd
    mulcomd
    oveq1d
    @6
    @38
    @8
    @4
    cA
    c.x
    co
    #
    c.x
    co
    #
    c.0
    @6
    @0
    @23
    @20
    @1
    @38
    @40
    wceq
    @19
    @32
    @21
    @35
    cX
    c.x
    cG
    @8
    @4
    cA
    odcl.1
    odid.3
    mulgnn0ass
    syl13anc
    @6
    @40
    @8
    c.0
    c.x
    co
    #
    c.0
    @6
    @39
    c.0
    @8
    c.x
    @6
    @1
    @39
    c.0
    wceq
    @35
    cA
    c.x
    cG
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    odid
    syl
    oveq2d
    @6
    @0
    @23
    @41
    c.0
    wceq
    @19
    @32
    cX
    c.x
    cG
    @8
    c.0
    odcl.1
    odid.3
    odid.4
    mulgnn0z
    syl2anc
    eqtrd
    eqtrd
    eqtrd
    oveq1d
    eqtrd
    @6
    @11
    cN
    cA
    c.x
    @6
    @11
    @9
    cN
    @9
    cmin
    co
    #
    caddc
    co
    cN
    @6
    @10
    @42
    @9
    caddc
    @6
    @28
    @26
    @10
    @42
    wceq
    @25
    @27
    cN
    @4
    modval
    syl2anc
    oveq2d
    @6
    @9
    cN
    @6
    @9
    @33
    nn0cnd
    @6
    cN
    @24
    nn0cnd
    pncan3d
    eqtrd
    oveq1d
    @6
    @0
    @13
    cX
    wcel
    #
    @15
    @13
    wceq
    @19
    @6
    @0
    @18
    @1
    @43
    @19
    @34
    @35
    cX
    c.x
    cG
    @10
    cA
    odcl.1
    odid.3
    mulgnn0cl
    syl3anc
    cX
    @14
    cG
    @13
    c.0
    odcl.1
    @36
    odid.4
    mndlid
    syl2anc
    3eqtr3rd
end
