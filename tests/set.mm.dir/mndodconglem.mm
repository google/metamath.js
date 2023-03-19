include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "c1.mm"
include "cfz.mm"
include "wcel.mm"
include "cn.mm"
include "nnred.mm"
include "recnd.mm"
include "nn0red.mm"
include "addsubassd.mm"
include "clt.mm"
include "nnzd.mm"
include "nn0zd.mm"
include "zaddcld.mm"
include "zred.mm"
include "cr.mm"
include "cn0.mm"
include "nn0addge1.mm"
include "syl2anc.mm"
include "ltletrd.mm"
include "cz.mm"
include "wb.mm"
include "znnsub.mm"
include "mpbid.mm"
include "eqeltrrd.mm"
include "addsub12d.mm"
include "oveq1d.mm"
include "cplusg.mm"
include "cmnd.mm"
include "nnnn0d.mm"
include "eqid.mm"
include "mulgnn0dir.mm"
include "syl13anc.mm"
include "3eqtr4d.mm"
include "pncan3d.mm"
include "odid.mm"
include "syl.mm"
include "eqtrd.mm"
include "odlem2.mm"
include "syl3anc.mm"
include "elfzle2.mm"
include "zsubcld.mm"
include "addge01d.mm"
include "mpbird.mm"
include "subge0d.mm"
include "wa.mm"
include "letri3d.mm"
include "biimprd.mm"
include "mpan2d.mm"
include "imp.mm"

theorem mndodconglem
  let wph: wff ph
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cM: class M
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
  assume mndodconglem.1: |- ( ph -> G e. Mnd )
  assume mndodconglem.2: |- ( ph -> A e. X )
  assume mndodconglem.3: |- ( ph -> ( O ` A ) e. NN )
  assume mndodconglem.4: |- ( ph -> M e. NN0 )
  assume mndodconglem.5: |- ( ph -> N e. NN0 )
  assume mndodconglem.6: |- ( ph -> M < ( O ` A ) )
  assume mndodconglem.7: |- ( ph -> N < ( O ` A ) )
  assume mndodconglem.8: |- ( ph -> ( M .x. A ) = ( N .x. A ) )


  assert |- ( ( ph /\ M <_ N ) -> M = N )

  proof
    wph
    cM
    cN
    cle
    wbr
    #
    cM
    cN
    wceq
    #
    wph
    @0
    cN
    cM
    cle
    wbr
    #
    @1
    wph
    cc0
    cM
    cN
    cmin
    co
    #
    cle
    wbr
    #
    @2
    wph
    @4
    cA
    cO
    cfv
    #
    @5
    @3
    caddc
    co
    #
    cle
    wbr
    #
    wph
    @5
    c1
    @6
    cfz
    co
    wcel
    #
    @7
    wph
    cA
    cX
    wcel
    #
    @6
    cn
    wcel
    @6
    cA
    c.x
    co
    #
    c.0
    wceq
    @8
    mndodconglem.2
    wph
    @5
    cM
    caddc
    co
    #
    cN
    cmin
    co
    #
    @6
    cn
    wph
    @5
    cM
    cN
    wph
    @5
    wph
    @5
    mndodconglem.3
    nnred
    #
    recnd
    #
    wph
    cM
    wph
    cM
    mndodconglem.4
    nn0red
    #
    recnd
    #
    wph
    cN
    wph
    cN
    mndodconglem.5
    nn0red
    #
    recnd
    #
    addsubassd
    wph
    cN
    @11
    clt
    wbr
    #
    @12
    cn
    wcel
    #
    wph
    cN
    @5
    @11
    @17
    @13
    wph
    @11
    wph
    @5
    cM
    wph
    @5
    mndodconglem.3
    nnzd
    #
    wph
    cM
    mndodconglem.4
    nn0zd
    #
    zaddcld
    #
    zred
    mndodconglem.7
    wph
    @5
    cr
    wcel
    cM
    cn0
    wcel
    #
    @5
    @11
    cle
    wbr
    @13
    mndodconglem.4
    @5
    cM
    nn0addge1
    syl2anc
    ltletrd
    wph
    cN
    cz
    wcel
    #
    @11
    cz
    wcel
    @19
    @20
    wb
    wph
    cN
    mndodconglem.5
    nn0zd
    #
    @23
    cN
    @11
    znnsub
    syl2anc
    mpbid
    eqeltrrd
    wph
    @10
    cM
    @5
    cN
    cmin
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
    wph
    @6
    @28
    cA
    c.x
    wph
    @5
    cM
    cN
    @14
    @16
    @18
    addsub12d
    oveq1d
    wph
    @29
    cN
    @27
    caddc
    co
    #
    cA
    c.x
    co
    #
    c.0
    wph
    cM
    cA
    c.x
    co
    #
    @27
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
    #
    @33
    @34
    co
    #
    @29
    @31
    wph
    @32
    @36
    @33
    @34
    mndodconglem.8
    oveq1d
    wph
    cG
    cmnd
    wcel
    #
    @24
    @27
    cn0
    wcel
    #
    @9
    @29
    @35
    wceq
    mndodconglem.1
    mndodconglem.4
    wph
    @27
    wph
    cN
    @5
    clt
    wbr
    #
    @27
    cn
    wcel
    #
    mndodconglem.7
    wph
    @25
    @5
    cz
    wcel
    @40
    @41
    wb
    @26
    @21
    cN
    @5
    znnsub
    syl2anc
    mpbid
    nnnn0d
    #
    mndodconglem.2
    cX
    @34
    c.x
    cG
    cM
    @27
    cA
    odcl.1
    odid.3
    @34
    eqid
    #
    mulgnn0dir
    syl13anc
    wph
    @38
    cN
    cn0
    wcel
    @39
    @9
    @31
    @37
    wceq
    mndodconglem.1
    mndodconglem.5
    @42
    mndodconglem.2
    cX
    @34
    c.x
    cG
    cN
    @27
    cA
    odcl.1
    odid.3
    @43
    mulgnn0dir
    syl13anc
    3eqtr4d
    wph
    @31
    @5
    cA
    c.x
    co
    #
    c.0
    wph
    @30
    @5
    cA
    c.x
    wph
    cN
    @5
    @18
    @14
    pncan3d
    oveq1d
    wph
    @9
    @44
    c.0
    wceq
    mndodconglem.2
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
    eqtrd
    eqtrd
    eqtrd
    cA
    c.x
    cG
    @6
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    odlem2
    syl3anc
    @5
    c1
    @6
    elfzle2
    syl
    wph
    @5
    @3
    @13
    wph
    @3
    wph
    cM
    cN
    @22
    @26
    zsubcld
    zred
    addge01d
    mpbird
    wph
    cM
    cN
    @15
    @17
    subge0d
    mpbid
    wph
    @1
    @0
    @2
    wa
    wph
    cM
    cN
    @15
    @17
    letri3d
    biimprd
    mpan2d
    imp
end
