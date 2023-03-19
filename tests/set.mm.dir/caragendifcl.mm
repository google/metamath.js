include "cuni.mm"
include "cdif.mm"
include "cdm.mm"
include "eqid.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "come.mm"
include "caragenss.mm"
include "syl.mm"
include "unissd.mm"
include "ssdifssd.mm"
include "cvv.mm"
include "wb.mm"
include "ccaragen.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "uniex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "a1i.mm"
include "elpwg.mm"
include "mpbird.mm"
include "cv.mm"
include "wa.mm"
include "cin.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "elpwi.mm"
include "adantl.mm"
include "caragenuni.mm"
include "eqcomd.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "difin2.mm"
include "incom.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "ssdifd.mm"
include "sscon.mm"
include "dfin4.mm"
include "eqimss2.mm"
include "sstrd.mm"
include "elinel1.mm"
include "wn.mm"
include "elinel2.mm"
include "elndif.mm"
include "eldifd.mm"
include "ssriv.mm"
include "eqssd.mm"
include "oveq12d.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cxr.mm"
include "iccssxr.mm"
include "omecl.mm"
include "sseldi.mm"
include "ssinss1.mm"
include "xaddcomd.mm"
include "wral.mm"
include "caragenel.mm"
include "mpbid.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "3eqtrd.mm"
include "carageneld.mm"

theorem caragendifcl
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cO: class O
  let va: setvar a
  let vx: setvar x
  let vk: setvar k
  assume caragendifcl.o: |- ( ph -> O e. OutMeas )
  assume caragendifcl.s: |- S = ( CaraGen ` O )
  assume caragendifcl.e: |- ( ph -> E e. S )


  assert |- ( ph -> ( U. S \ E ) e. S )

  proof
    wph
    cS
    cS
    cuni
    #
    cE
    cdif
    #
    cO
    cO
    cdm
    #
    cuni
    #
    va
    caragendifcl.o
    @3
    eqid
    #
    caragendifcl.s
    wph
    @1
    @3
    cpw
    #
    wcel
    #
    @1
    @3
    wss
    #
    wph
    @0
    @3
    cE
    wph
    cS
    @2
    wph
    cO
    come
    wcel
    #
    cS
    @2
    wss
    caragendifcl.o
    cS
    cO
    caragendifcl.s
    caragenss
    syl
    unissd
    ssdifssd
    wph
    @1
    cvv
    wcel
    #
    @6
    @7
    wb
    @9
    wph
    @0
    cvv
    wcel
    @9
    cS
    cS
    cO
    ccaragen
    cfv
    cvv
    caragendifcl.s
    cO
    ccaragen
    fvex
    eqeltri
    uniex
    @0
    cE
    cvv
    difexg
    ax-mp
    a1i
    @1
    @3
    cvv
    elpwg
    syl
    mpbird
    wph
    va
    cv
    #
    @5
    wcel
    #
    wa
    #
    @10
    @1
    cin
    #
    cO
    cfv
    #
    @10
    @1
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    @10
    cE
    cdif
    #
    cO
    cfv
    #
    @10
    cE
    cin
    #
    cO
    cfv
    #
    cxad
    co
    @20
    @18
    cxad
    co
    #
    @10
    cO
    cfv
    #
    @12
    @14
    @18
    @16
    @20
    cxad
    @12
    @13
    @17
    cO
    @12
    @17
    @1
    @10
    cin
    #
    @13
    @12
    @10
    @0
    wss
    @17
    @23
    wceq
    @12
    @10
    @3
    @0
    @11
    @10
    @3
    wss
    #
    wph
    @10
    @3
    elpwi
    #
    adantl
    #
    wph
    @3
    @0
    wceq
    @11
    wph
    @0
    @3
    wph
    cS
    cO
    caragendifcl.o
    caragendifcl.s
    caragenuni
    eqcomd
    adantr
    sseqtrd
    #
    @10
    cE
    @0
    difin2
    syl
    @23
    @13
    wceq
    @12
    @1
    @10
    incom
    a1i
    eqtr2d
    fveq2d
    @12
    @15
    @19
    cO
    @12
    @15
    @19
    @12
    @15
    @10
    @17
    cdif
    #
    @19
    @12
    @17
    @1
    wss
    @15
    @28
    wss
    @12
    @10
    @0
    cE
    @27
    ssdifd
    @17
    @1
    @10
    sscon
    syl
    @12
    @19
    @28
    wceq
    #
    @28
    @19
    wss
    @29
    @12
    @10
    cE
    dfin4
    a1i
    @28
    @19
    eqimss2
    syl
    sstrd
    @19
    @15
    wss
    @12
    vx
    @19
    @15
    vx
    cv
    #
    @19
    wcel
    #
    @30
    @10
    @1
    @30
    @10
    cE
    elinel1
    @31
    @30
    cE
    wcel
    @30
    @1
    wcel
    wn
    @30
    @10
    cE
    elinel2
    @30
    cE
    @0
    elndif
    syl
    eldifd
    ssriv
    a1i
    eqssd
    fveq2d
    oveq12d
    @12
    @18
    @20
    @12
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @18
    cc0
    cpnf
    iccssxr
    #
    @12
    @17
    cO
    @3
    wph
    @8
    @11
    caragendifcl.o
    adantr
    #
    @4
    @12
    @10
    @3
    cE
    @26
    ssdifssd
    omecl
    sseldi
    @12
    @32
    cxr
    @20
    @33
    @12
    @19
    cO
    @3
    @34
    @4
    @11
    @19
    @3
    wss
    #
    wph
    @11
    @24
    @35
    @25
    @10
    cE
    @3
    ssinss1
    syl
    adantl
    omecl
    sseldi
    xaddcomd
    wph
    @21
    @22
    wceq
    #
    va
    @5
    wph
    cE
    @5
    wcel
    #
    @36
    va
    @5
    wral
    #
    wph
    cE
    cS
    wcel
    @37
    @38
    wa
    caragendifcl.e
    wph
    cS
    cE
    cO
    va
    caragendifcl.o
    caragendifcl.s
    caragenel
    mpbid
    simprd
    r19.21bi
    3eqtrd
    carageneld
end
