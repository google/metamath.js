include "ciun.mm"
include "cfv.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "nfmpt1.mm"
include "cpw.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cvv.mm"
include "wb.mm"
include "come.mm"
include "unidmex.mm"
include "adantr.mm"
include "ssexg.mm"
include "syl2anc.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "eqid.mm"
include "fmptdf.mm"
include "omeiunle.mm"
include "wceq.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "eqcomd.mm"
include "iuneq2df.mm"
include "fveq2d.mm"
include "mpteq2da.mm"
include "breq12d.mm"

theorem omeiunlempt
  let wph: wff ph
  let vn: setvar n
  let cE: class E
  let cN: class N
  let cO: class O
  let cX: class X
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume omeiunlempt.nph: |- F/ n ph
  assume omeiunlempt.o: |- ( ph -> O e. OutMeas )
  assume omeiunlempt.x: |- X = U. dom O
  assume omeiunlempt.z: |- Z = ( ZZ>= ` N )
  assume omeiunlempt.e: |- ( ( ph /\ n e. Z ) -> E C_ X )

  disjoint O n
  disjoint X n
  disjoint Z n
  disjoint k x
  assert |- ( ph -> ( O ` U_ n e. Z E ) <_ ( sum^ ` ( n e. Z |-> ( O ` E ) ) ) )

  proof
    wph
    vn
    cZ
    cE
    ciun
    #
    cO
    cfv
    #
    vn
    cZ
    cE
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    vn
    cZ
    vn
    cv
    #
    vn
    cZ
    cE
    cmpt
    #
    cfv
    #
    ciun
    #
    cO
    cfv
    #
    vn
    cZ
    @7
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    wph
    vn
    @6
    cN
    cO
    cX
    cZ
    omeiunlempt.nph
    vn
    cZ
    cE
    nfmpt1
    omeiunlempt.o
    omeiunlempt.x
    omeiunlempt.z
    wph
    vn
    cZ
    cE
    cX
    cpw
    #
    @6
    omeiunlempt.nph
    wph
    @5
    cZ
    wcel
    #
    wa
    #
    cE
    @13
    wcel
    #
    cE
    cX
    wss
    #
    omeiunlempt.e
    @15
    cE
    cvv
    wcel
    #
    @16
    @17
    wb
    @15
    @17
    cX
    cvv
    wcel
    #
    @18
    omeiunlempt.e
    wph
    @19
    @14
    wph
    cO
    come
    cX
    omeiunlempt.o
    omeiunlempt.x
    unidmex
    adantr
    cE
    cX
    cvv
    ssexg
    syl2anc
    #
    cE
    cX
    cvv
    elpwg
    syl
    mpbird
    @6
    eqid
    #
    fmptdf
    omeiunle
    wph
    @1
    @9
    @4
    @12
    cle
    wph
    @0
    @8
    cO
    wph
    vn
    cZ
    cE
    @7
    omeiunlempt.nph
    @15
    @7
    cE
    @15
    @14
    @18
    @7
    cE
    wceq
    wph
    @14
    simpr
    @20
    vn
    cZ
    cE
    cvv
    @6
    @21
    fvmpt2
    syl2anc
    eqcomd
    #
    iuneq2df
    fveq2d
    wph
    @3
    @11
    csumge0
    wph
    vn
    cZ
    @2
    @10
    omeiunlempt.nph
    @15
    cE
    @7
    cO
    @22
    fveq2d
    mpteq2da
    fveq2d
    breq12d
    mpbird
end
