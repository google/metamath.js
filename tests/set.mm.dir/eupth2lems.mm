include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "cop.mm"
include "cvtxdg.mm"
include "cdvds.mm"
include "wn.mm"
include "crab.mm"
include "wceq.mm"
include "c0.mm"
include "cpr.mm"
include "cif.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "cr.mm"
include "nn0re.mm"
include "adantl.mm"
include "lep1d.mm"
include "peano2re.mm"
include "syl.mm"
include "ceupth.mm"
include "cwlks.mm"
include "eupthiswlk.mm"
include "wlkcl.mm"
include "3syl.mm"
include "nn0red.mm"
include "adantr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "imim1d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "notbid.mm"
include "elrab.mm"
include "cupgr.mm"
include "ad3antrrr.mm"
include "wfun.mm"
include "eqid.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simplrr.mm"
include "eupth2lem3.mm"
include "pm5.32da.mm"
include "cpw.mm"
include "0elpw.mm"
include "wss.mm"
include "wlkepvtx.mm"
include "simpld.mm"
include "cfz.mm"
include "wf.mm"
include "wlkp.mm"
include "cuz.mm"
include "cz.mm"
include "wb.mm"
include "peano2nn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nn0zd.mm"
include "elfz5.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ffvelrnd.mm"
include "prssd.mm"
include "prex.mm"
include "elpw.mm"
include "sylibr.mm"
include "ifcl.mm"
include "sylancr.mm"
include "elpwid.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "bitr4d.mm"
include "syl5bb.mm"
include "eqrdv.mm"
include "exp32.mm"
include "a2d.mm"
include "syld.mm"

theorem eupth2lems
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vy: setvar y
  assume eupth2.v: |- V = ( Vtx ` G )
  assume eupth2.i: |- I = ( iEdg ` G )
  assume eupth2.g: |- ( ph -> G e. UPGraph )
  assume eupth2.f: |- ( ph -> Fun I )
  assume eupth2.p: |- ( ph -> F ( EulerPaths ` G ) P )

  disjoint ph x
  disjoint F x
  disjoint I x
  disjoint V x
  disjoint n x
  disjoint F y
  disjoint x y
  disjoint I y
  disjoint P y
  disjoint V y
  disjoint n y
  disjoint ph y
  assert |- ( ( ph /\ n e. NN0 ) -> ( ( n <_ ( # ` F ) -> { x e. V | -. 2 || ( ( VtxDeg ` <. V , ( I |` ( F " ( 0 ..^ n ) ) ) >. ) ` x ) } = if ( ( P ` 0 ) = ( P ` n ) , (/) , { ( P ` 0 ) , ( P ` n ) } ) ) -> ( ( n + 1 ) <_ ( # ` F ) -> { x e. V | -. 2 || ( ( VtxDeg ` <. V , ( I |` ( F " ( 0 ..^ ( n + 1 ) ) ) ) >. ) ` x ) } = if ( ( P ` 0 ) = ( P ` ( n + 1 ) ) , (/) , { ( P ` 0 ) , ( P ` ( n + 1 ) ) } ) ) ) )

  proof
    wph
    vn
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @0
    cF
    chash
    cfv
    #
    cle
    wbr
    #
    c2
    vx
    cv
    #
    cV
    cI
    cF
    cc0
    @0
    cfzo
    co
    cima
    cres
    cop
    #
    cvtxdg
    cfv
    cfv
    cdvds
    wbr
    wn
    vx
    cV
    crab
    cc0
    cP
    cfv
    #
    @0
    cP
    cfv
    #
    wceq
    c0
    @7
    @8
    cpr
    cif
    wceq
    #
    wi
    @0
    c1
    caddc
    co
    #
    @3
    cle
    wbr
    #
    @9
    wi
    @11
    c2
    @5
    cV
    cI
    cF
    cc0
    @10
    cfzo
    co
    cima
    cres
    cop
    #
    cvtxdg
    cfv
    #
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vx
    cV
    crab
    #
    @7
    @10
    cP
    cfv
    #
    wceq
    #
    c0
    @7
    @18
    cpr
    #
    cif
    #
    wceq
    #
    wi
    @2
    @11
    @4
    @9
    @2
    @0
    @10
    cle
    wbr
    #
    @11
    @4
    @2
    @0
    @1
    @0
    cr
    wcel
    #
    wph
    @0
    nn0re
    adantl
    #
    lep1d
    @2
    @24
    @10
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @23
    @11
    wa
    @4
    wi
    @25
    @2
    @24
    @26
    @25
    @0
    peano2re
    syl
    wph
    @27
    @1
    wph
    @3
    wph
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @3
    cn0
    wcel
    #
    eupth2.p
    cP
    cF
    cG
    eupthiswlk
    #
    cP
    cF
    cG
    wlkcl
    3syl
    #
    nn0red
    adantr
    @0
    @10
    @3
    letr
    syl3anc
    mpand
    imim1d
    @2
    @11
    @9
    @22
    @2
    @11
    @9
    @22
    @2
    @11
    @9
    wa
    #
    wa
    #
    vy
    @17
    @21
    vy
    cv
    #
    @17
    wcel
    @35
    cV
    wcel
    #
    c2
    @35
    @13
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    @34
    @35
    @21
    wcel
    #
    @16
    @39
    vx
    @35
    cV
    @5
    @35
    wceq
    #
    @15
    @38
    @42
    @14
    @37
    c2
    cdvds
    @5
    @35
    @13
    fveq2
    breq2d
    notbid
    elrab
    @34
    @40
    @36
    @41
    wa
    @41
    @34
    @36
    @39
    @41
    @34
    @36
    wa
    vx
    cP
    @35
    cF
    cG
    @6
    cI
    @0
    cV
    @12
    eupth2.v
    eupth2.i
    wph
    cG
    cupgr
    wcel
    @1
    @33
    @36
    eupth2.g
    ad3antrrr
    wph
    cI
    wfun
    @1
    @33
    @36
    eupth2.f
    ad3antrrr
    wph
    @28
    @1
    @33
    @36
    eupth2.p
    ad3antrrr
    @6
    eqid
    @12
    eqid
    @2
    @1
    @33
    @36
    wph
    @1
    simpr
    ad2antrr
    @34
    @11
    @36
    @2
    @11
    @9
    simprl
    #
    adantr
    @34
    @36
    simpr
    @2
    @11
    @9
    @36
    simplrr
    eupth2lem3
    pm5.32da
    @34
    @41
    @36
    @34
    @21
    cV
    @35
    @34
    @21
    cV
    @34
    c0
    cV
    cpw
    #
    wcel
    @20
    @44
    wcel
    #
    @21
    @44
    wcel
    cV
    0elpw
    @34
    @20
    cV
    wss
    @45
    @34
    @7
    @18
    cV
    wph
    @7
    cV
    wcel
    #
    @1
    @33
    wph
    @28
    @29
    @46
    eupth2.p
    @31
    @29
    @46
    @3
    cP
    cfv
    cV
    wcel
    cP
    cF
    cG
    cV
    eupth2.v
    wlkepvtx
    simpld
    3syl
    ad2antrr
    @34
    cc0
    @3
    cfz
    co
    #
    cV
    @10
    cP
    wph
    @47
    cV
    cP
    wf
    #
    @1
    @33
    wph
    @28
    @29
    @48
    eupth2.p
    @31
    cP
    cF
    cG
    cV
    eupth2.v
    wlkp
    3syl
    ad2antrr
    @34
    @10
    @47
    wcel
    #
    @11
    @43
    @34
    @10
    cc0
    cuz
    cfv
    #
    wcel
    @3
    cz
    wcel
    @49
    @11
    wb
    @34
    @10
    cn0
    @50
    @2
    @10
    cn0
    wcel
    #
    @33
    @1
    @51
    wph
    @0
    peano2nn0
    adantl
    adantr
    nn0uz
    syl6eleq
    @34
    @3
    wph
    @30
    @1
    @33
    @32
    ad2antrr
    nn0zd
    @10
    cc0
    @3
    elfz5
    syl2anc
    mpbird
    ffvelrnd
    prssd
    @20
    cV
    @7
    @18
    prex
    elpw
    sylibr
    @19
    c0
    @20
    @44
    ifcl
    sylancr
    elpwid
    sseld
    pm4.71rd
    bitr4d
    syl5bb
    eqrdv
    exp32
    a2d
    syld
end
