include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "mvrf.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "adantr.mm"
include "wn.mm"
include "w3a.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "simp2r.mm"
include "fveq1d.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "crg.mm"
include "eqid.mm"
include "3ad2ant1.mm"
include "simp2ll.mm"
include "mvrid.mm"
include "simp2lr.mm"
include "1nn0.mm"
include "snifpsrbag.mm"
include "sylancl.mm"
include "mvrval2.mm"
include "3eqtr3d.mm"
include "simp3.mm"
include "wb.mm"
include "mpteqb.mm"
include "0nn0.mm"
include "keepel.mm"
include "a1i.mm"
include "mprg.mm"
include "iftrue.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "syl5bi.mm"
include "syl.mm"
include "ax-1ne0.mm"
include "necon3abid.mm"
include "mpbii.mm"
include "iffalse.mm"
include "nsyl2.mm"
include "syl6.mm"
include "mtod.mm"
include "eqtrd.mm"
include "3expia.mm"
include "necon1ad.mm"
include "mpd.mm"
include "expr.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem mvrf1
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let cI: class I
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mvrf.s: |- S = ( I mPwSer R )
  assume mvrf.v: |- V = ( I mVar R )
  assume mvrf.b: |- B = ( Base ` S )
  assume mvrf.i: |- ( ph -> I e. W )
  assume mvrf.r: |- ( ph -> R e. Ring )
  assume mvrf1.z: |- .0. = ( 0g ` R )
  assume mvrf1.o: |- .1. = ( 1r ` R )
  assume mvrf1.n: |- ( ph -> .1. =/= .0. )


  assert |- ( ph -> V : I -1-1-> B )

  proof
    wph
    cI
    cB
    cV
    wf
    vx
    cv
    #
    cV
    cfv
    #
    vy
    cv
    #
    cV
    cfv
    #
    wceq
    #
    @0
    @2
    wceq
    #
    wi
    #
    vy
    cI
    wral
    vx
    cI
    wral
    cI
    cB
    cV
    wf1
    wph
    cB
    cR
    cS
    cI
    cV
    cW
    mvrf.s
    mvrf.v
    mvrf.b
    mvrf.i
    mvrf.r
    mvrf
    wph
    @6
    vx
    vy
    cI
    cI
    wph
    @0
    cI
    wcel
    #
    @2
    cI
    wcel
    #
    wa
    #
    @4
    @5
    wph
    @9
    @4
    wa
    #
    wa
    #
    c.1
    c.0
    wne
    #
    @5
    wph
    @12
    @10
    mvrf1.n
    adantr
    @11
    @5
    c.1
    c.0
    wph
    @10
    @5
    wn
    #
    c.1
    c.0
    wceq
    wph
    @10
    @13
    w3a
    #
    c.1
    vz
    cI
    vz
    cv
    #
    @0
    wceq
    #
    c1
    cc0
    cif
    #
    cmpt
    #
    vz
    cI
    @15
    @2
    wceq
    #
    c1
    cc0
    cif
    #
    cmpt
    wceq
    #
    c.1
    c.0
    cif
    #
    c.0
    @14
    @18
    @1
    cfv
    @18
    @3
    cfv
    c.1
    @22
    @14
    @18
    @1
    @3
    wph
    @9
    @4
    @13
    simp2r
    fveq1d
    @14
    vz
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    cI
    cmap
    co
    crab
    #
    cR
    c.1
    vh
    cI
    cV
    cW
    @0
    crg
    c.0
    mvrf.v
    @23
    eqid
    #
    mvrf1.z
    mvrf1.o
    wph
    @10
    cI
    cW
    wcel
    #
    @13
    mvrf.i
    3ad2ant1
    #
    wph
    @10
    cR
    crg
    wcel
    @13
    mvrf.r
    3ad2ant1
    #
    @7
    @8
    @4
    wph
    @13
    simp2ll
    #
    mvrid
    @14
    vz
    @23
    cR
    c.1
    vh
    @18
    cI
    cV
    cW
    @2
    crg
    c.0
    mvrf.v
    @24
    mvrf1.z
    mvrf1.o
    @26
    @27
    @7
    @8
    @4
    wph
    @13
    simp2lr
    @14
    @25
    c1
    cn0
    wcel
    @18
    @23
    wcel
    @26
    1nn0
    vz
    @23
    vh
    cI
    c1
    cW
    @0
    @24
    snifpsrbag
    sylancl
    mvrval2
    3eqtr3d
    @14
    @21
    wn
    @22
    c.0
    wceq
    @14
    @21
    @5
    wph
    @10
    @13
    simp3
    @14
    @21
    c1
    @5
    c1
    cc0
    cif
    #
    wceq
    #
    @5
    @14
    @7
    @21
    @30
    wi
    @28
    @21
    @17
    @20
    wceq
    #
    vz
    cI
    wral
    #
    @7
    @30
    @17
    cn0
    wcel
    #
    @21
    @32
    wb
    vz
    cI
    vz
    cI
    @17
    @20
    cn0
    mpteqb
    @33
    @15
    cI
    wcel
    @16
    c1
    cc0
    cn0
    1nn0
    0nn0
    keepel
    a1i
    mprg
    @31
    @30
    vz
    @0
    cI
    @16
    @17
    c1
    @20
    @29
    @16
    c1
    cc0
    iftrue
    @16
    @19
    @5
    c1
    cc0
    @15
    @0
    @2
    eqeq1
    ifbid
    eqeq12d
    rspcv
    syl5bi
    syl
    @30
    @29
    cc0
    wceq
    #
    @5
    @30
    c1
    cc0
    wne
    @34
    wn
    ax-1ne0
    @30
    @34
    c1
    cc0
    c1
    @29
    cc0
    eqeq1
    necon3abid
    mpbii
    @5
    c1
    cc0
    iffalse
    nsyl2
    syl6
    mtod
    @21
    c.1
    c.0
    iffalse
    syl
    eqtrd
    3expia
    necon1ad
    mpd
    expr
    ralrimivva
    vx
    vy
    cI
    cB
    cV
    dff13
    sylanbrc
end
