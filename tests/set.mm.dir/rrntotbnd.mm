include "cfn.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cr.mm"
include "cress.mm"
include "co.mm"
include "cpws.mm"
include "cds.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "chash.mm"
include "csqrt.mm"
include "c1.mm"
include "caddc.mm"
include "crrn.mm"
include "eqid.mm"
include "repwsmet.mm"
include "rrnmet.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "resqrtcld.mm"
include "syl.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "sqrtge0d.mm"
include "ge0p1rpd.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "cmul.mm"
include "cme.mm"
include "metcl.mm"
include "3expb.mm"
include "sylan.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "w3a.mm"
include "metge0.mm"
include "jca.mm"
include "syl3anc.mm"
include "simpld.mm"
include "remulcld.mm"
include "peano2re.mm"
include "id.mm"
include "rrnequiv.mm"
include "simprd.mm"
include "lep1d.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "letrd.mm"
include "recnd.mm"
include "mulid2d.mm"
include "breqtrrd.mm"
include "cc.mm"
include "wss.mm"
include "ctotbnd.mm"
include "cbnd.mm"
include "wb.mm"
include "ax-resscn.mm"
include "cnpwstotbnd.mm"
include "mpan.mm"
include "equivbnd2.mm"

theorem rrntotbnd
  let cI: class I
  let cM: class M
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume rrntotbnd.1: |- X = ( RR ^m I )
  assume rrntotbnd.2: |- M = ( ( Rn ` I ) |` ( Y X. Y ) )


  assert |- ( I e. Fin -> ( M e. ( TotBnd ` Y ) <-> M e. ( Bnd ` Y ) ) )

  proof
    cI
    cfn
    wcel
    #
    vx
    vy
    ccnfld
    cr
    cress
    co
    cI
    cpws
    co
    #
    cds
    cfv
    #
    cY
    cY
    cxp
    cres
    #
    cM
    cI
    chash
    cfv
    #
    csqrt
    cfv
    #
    c1
    caddc
    co
    #
    c1
    @2
    cI
    crrn
    cfv
    #
    cX
    cY
    @2
    cI
    cX
    @1
    @1
    eqid
    #
    @2
    eqid
    #
    rrntotbnd.1
    repwsmet
    #
    cI
    cX
    rrntotbnd.1
    rrnmet
    #
    @0
    @5
    @0
    @4
    cn0
    wcel
    #
    @5
    cr
    wcel
    #
    cI
    hashcl
    #
    @12
    @4
    @4
    nn0re
    #
    @4
    nn0ge0
    #
    resqrtcld
    syl
    #
    @0
    @12
    cc0
    @5
    cle
    wbr
    @14
    @12
    @4
    @15
    @16
    sqrtge0d
    syl
    ge0p1rpd
    c1
    crp
    wcel
    @0
    1rp
    a1i
    @0
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cX
    wcel
    #
    wa
    #
    wa
    #
    @18
    @20
    @7
    co
    #
    @5
    @18
    @20
    @2
    co
    #
    cmul
    co
    #
    @6
    @25
    cmul
    co
    #
    @0
    @7
    cX
    cme
    cfv
    #
    wcel
    #
    @22
    @24
    cr
    wcel
    #
    @11
    @29
    @19
    @21
    @30
    @18
    @20
    @7
    cX
    metcl
    3expb
    sylan
    #
    @23
    @5
    @25
    @0
    @13
    @22
    @17
    adantr
    #
    @23
    @25
    cr
    wcel
    #
    cc0
    @25
    cle
    wbr
    #
    @23
    @2
    @28
    wcel
    #
    @19
    @21
    @33
    @34
    wa
    #
    @0
    @35
    @22
    @10
    adantr
    @0
    @19
    @21
    simprl
    @0
    @19
    @21
    simprr
    @35
    @19
    @21
    w3a
    @33
    @34
    @18
    @20
    @2
    cX
    metcl
    @18
    @20
    @2
    cX
    metge0
    jca
    syl3anc
    #
    simpld
    #
    remulcld
    @23
    @6
    @25
    @0
    @6
    cr
    wcel
    #
    @22
    @0
    @13
    @39
    @17
    @5
    peano2re
    syl
    adantr
    #
    @38
    remulcld
    @23
    @25
    @24
    cle
    wbr
    #
    @24
    @26
    cle
    wbr
    #
    @0
    @2
    @18
    @20
    cI
    cX
    @1
    @8
    @9
    rrntotbnd.1
    @0
    id
    rrnequiv
    #
    simprd
    @23
    @13
    @39
    @36
    @5
    @6
    cle
    wbr
    @26
    @27
    cle
    wbr
    @32
    @40
    @37
    @23
    @5
    @32
    lep1d
    @5
    @6
    @25
    lemul1a
    syl31anc
    letrd
    @23
    @25
    @24
    c1
    @24
    cmul
    co
    cle
    @23
    @41
    @42
    @43
    simpld
    @23
    @24
    @23
    @24
    @31
    recnd
    mulid2d
    breqtrrd
    @3
    eqid
    #
    rrntotbnd.2
    cr
    cc
    wss
    @0
    @3
    cY
    ctotbnd
    cfv
    wcel
    @3
    cY
    cbnd
    cfv
    wcel
    wb
    ax-resscn
    cr
    @3
    cI
    cY
    @1
    @8
    @44
    cnpwstotbnd
    mpan
    equivbnd2
end
