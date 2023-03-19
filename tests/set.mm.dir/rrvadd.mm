include "caddc.mm"
include "cof.mm"
include "co.mm"
include "crrv.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cbrsiga.mm"
include "cmbfm.mm"
include "cr.mm"
include "cv.mm"
include "cmpt2.mm"
include "cuni.mm"
include "cop.mm"
include "cmpt.mm"
include "ccom.mm"
include "nfmpt1.mm"
include "rrvvf.mm"
include "unveldomd.mm"
include "eqidd.mm"
include "ofoprabco.mm"
include "csx.mm"
include "cprb.mm"
include "csiga.mm"
include "crn.mm"
include "domprobsiga.mm"
include "syl.mm"
include "brsigarn.mm"
include "elrnsiga.mm"
include "mp1i.mm"
include "sxsiga.mm"
include "syl2anc.mm"
include "rrvmbfm.mm"
include "mpbid.mm"
include "wceq.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "cbvmptv.mm"
include "mbfmco2.mm"
include "cioo.mm"
include "ctg.mm"
include "ctx.mm"
include "ccn.mm"
include "eqid.mm"
include "raddcn.mm"
include "a1i.mm"
include "csigagen.mm"
include "sxbrsiga.mm"
include "df-brsiga.mm"
include "cnmbfm.mm"
include "mbfmco.mm"
include "eqeltrd.mm"
include "mpbird.mm"

theorem rrvadd
  let wph: wff ph
  let cP: class P
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume rrvadd.1: |- ( ph -> P e. Prob )
  assume rrvadd.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume rrvadd.3: |- ( ph -> Y e. ( rRndVar ` P ) )


  assert |- ( ph -> ( X oF + Y ) e. ( rRndVar ` P ) )

  proof
    wph
    cX
    cY
    caddc
    cof
    co
    #
    cP
    crrv
    cfv
    #
    wcel
    @0
    cP
    cdm
    #
    cbrsiga
    cmbfm
    co
    #
    wcel
    wph
    @0
    vx
    vy
    cr
    cr
    vx
    cv
    vy
    cv
    caddc
    co
    cmpt2
    #
    va
    @2
    cuni
    #
    va
    cv
    #
    cX
    cfv
    #
    @6
    cY
    cfv
    #
    cop
    #
    cmpt
    #
    ccom
    @3
    wph
    vx
    vy
    @5
    cr
    cr
    caddc
    cX
    cY
    @10
    @4
    @2
    va
    va
    @5
    @9
    nfmpt1
    wph
    cP
    cX
    rrvadd.1
    rrvadd.2
    rrvvf
    wph
    cP
    cY
    rrvadd.1
    rrvadd.3
    rrvvf
    wph
    cP
    rrvadd.1
    unveldomd
    wph
    @10
    eqidd
    wph
    @4
    eqidd
    ofoprabco
    wph
    @2
    cbrsiga
    cbrsiga
    csx
    co
    #
    cbrsiga
    @10
    @4
    wph
    cP
    cprb
    wcel
    @2
    csiga
    crn
    cuni
    #
    wcel
    rrvadd.1
    cP
    domprobsiga
    syl
    #
    wph
    cbrsiga
    @12
    wcel
    #
    @14
    @11
    @12
    wcel
    cbrsiga
    cr
    csiga
    cfv
    wcel
    @14
    wph
    brsigarn
    cbrsiga
    cr
    elrnsiga
    mp1i
    #
    @15
    cbrsiga
    cbrsiga
    sxsiga
    syl2anc
    @15
    wph
    vb
    @2
    cbrsiga
    cbrsiga
    cX
    cY
    @10
    @13
    @15
    @15
    wph
    cX
    @1
    wcel
    cX
    @3
    wcel
    rrvadd.2
    wph
    cP
    cX
    rrvadd.1
    rrvmbfm
    mpbid
    wph
    cY
    @1
    wcel
    cY
    @3
    wcel
    rrvadd.3
    wph
    cP
    cY
    rrvadd.1
    rrvmbfm
    mpbid
    va
    vb
    @5
    @9
    vb
    cv
    #
    cX
    cfv
    #
    @16
    cY
    cfv
    #
    cop
    @6
    @16
    wceq
    @7
    @17
    @8
    @18
    @6
    @16
    cX
    fveq2
    @6
    @16
    cY
    fveq2
    opeq12d
    cbvmptv
    mbfmco2
    wph
    @11
    cbrsiga
    @4
    cioo
    crn
    ctg
    cfv
    #
    @19
    ctx
    co
    #
    @19
    @4
    @20
    @19
    ccn
    co
    wcel
    wph
    vx
    vy
    @19
    @19
    eqid
    #
    raddcn
    a1i
    @11
    @20
    csigagen
    cfv
    wceq
    wph
    @19
    @21
    sxbrsiga
    a1i
    cbrsiga
    @19
    csigagen
    cfv
    wceq
    wph
    df-brsiga
    a1i
    cnmbfm
    mbfmco
    eqeltrd
    wph
    cP
    @0
    rrvadd.1
    rrvmbfm
    mpbird
end
