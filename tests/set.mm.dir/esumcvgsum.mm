include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "cmpt.mm"
include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "simpll.mm"
include "elfznn.mm"
include "adantl.mm"
include "syl2anc.mm"
include "cuz.mm"
include "nnuz.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cr.mm"
include "cmnf.mm"
include "cioo.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wss.mm"
include "mnfxr.mm"
include "pnfxr.mm"
include "0re.mm"
include "mnflt.mm"
include "ax-mp.mm"
include "pnfge.mm"
include "icossioo.mm"
include "mp4an.mm"
include "ioomax.mm"
include "sseqtri.mm"
include "sseldi.mm"
include "recnd.mm"
include "fsumser.mm"
include "mpteq2dva.mm"
include "wfn.mm"
include "cz.mm"
include "1z.mm"
include "seqfn.mm"
include "wb.mm"
include "fneq2.mm"
include "mpbir.mm"
include "dffn5.mm"
include "mpbi.mm"
include "cvv.mm"
include "seqex.mm"
include "a1i.mm"
include "breldmg.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"
include "eqeltrd.mm"
include "esumpcvgval.mm"

theorem esumcvgsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vk: setvar k
  let cF: class F
  let cL: class L
  let vj: setvar j
  assume esumcvgsum.1: |- ( k = i -> A = B )
  assume esumcvgsum.2: |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,) +oo ) )
  assume esumcvgsum.3: |- ( ( ph /\ k e. NN ) -> ( F ` k ) = A )
  assume esumcvgsum.4: |- ( ph -> seq 1 ( + , F ) ~~> L )
  assume esumcvgsum.5: |- ( ph -> L e. RR )

  disjoint i k
  disjoint A i
  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint i j
  disjoint j k
  disjoint A j
  disjoint B j
  disjoint F j
  disjoint j ph
  assert |- ( ph -> sum* k e. NN A = sum_ k e. NN A )

  proof
    wph
    cA
    cB
    vk
    vj
    vi
    esumcvgsum.2
    esumcvgsum.1
    wph
    vj
    cn
    c1
    vj
    cv
    #
    cfz
    co
    #
    cA
    vk
    csu
    #
    cmpt
    vj
    cn
    @0
    caddc
    cF
    c1
    cseq
    #
    cfv
    #
    cmpt
    #
    cli
    cdm
    #
    wph
    vj
    cn
    @2
    @4
    wph
    @0
    cn
    wcel
    #
    wa
    #
    cA
    vk
    cF
    c1
    @0
    @8
    vk
    cv
    #
    @1
    wcel
    #
    wa
    #
    wph
    @9
    cn
    wcel
    #
    @9
    cF
    cfv
    cA
    wceq
    wph
    @7
    @10
    simpll
    #
    @10
    @12
    @8
    @9
    @0
    elfznn
    adantl
    #
    esumcvgsum.3
    syl2anc
    @7
    @0
    c1
    cuz
    cfv
    #
    wcel
    #
    wph
    @7
    @16
    cn
    @15
    @0
    nnuz
    eleq2i
    biimpi
    adantl
    @11
    cA
    @11
    cc0
    cpnf
    cico
    co
    #
    cr
    cA
    @17
    cmnf
    cpnf
    cioo
    co
    #
    cr
    cmnf
    cxr
    wcel
    cpnf
    cxr
    wcel
    #
    cmnf
    cc0
    clt
    wbr
    #
    cpnf
    cpnf
    cle
    wbr
    #
    @17
    @18
    wss
    mnfxr
    pnfxr
    cc0
    cr
    wcel
    @20
    0re
    cc0
    mnflt
    ax-mp
    @19
    @21
    pnfxr
    cpnf
    pnfge
    ax-mp
    cmnf
    cpnf
    cc0
    cpnf
    icossioo
    mp4an
    ioomax
    sseqtri
    @11
    wph
    @12
    cA
    @17
    wcel
    @13
    @14
    esumcvgsum.2
    syl2anc
    sseldi
    recnd
    fsumser
    mpteq2dva
    wph
    @5
    @3
    @6
    @3
    cn
    wfn
    #
    @3
    @5
    wceq
    @22
    @3
    @15
    wfn
    #
    c1
    cz
    wcel
    @23
    1z
    caddc
    cF
    c1
    seqfn
    ax-mp
    cn
    @15
    wceq
    @22
    @23
    wb
    nnuz
    cn
    @15
    @3
    fneq2
    ax-mp
    mpbir
    vj
    cn
    @3
    dffn5
    mpbi
    wph
    @3
    cvv
    wcel
    #
    cL
    cr
    wcel
    @3
    cL
    cli
    wbr
    @3
    @6
    wcel
    @24
    wph
    caddc
    cF
    c1
    seqex
    a1i
    esumcvgsum.5
    esumcvgsum.4
    @3
    cL
    cvv
    cr
    cli
    breldmg
    syl3anc
    syl5eqelr
    eqeltrd
    esumpcvgval
end
