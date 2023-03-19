include "cr.mm"
include "wf.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "csupp.mm"
include "co.mm"
include "cfdiv.mm"
include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "wa.mm"
include "simpl1.mm"
include "wss.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "3ad2ant2.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "simpl2.mm"
include "wne.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "simp3.mm"
include "0red.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "simplbda.mm"
include "redivcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cc.mm"
include "wceq.mm"
include "id.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "fssd.mm"
include "3anim123i.mm"
include "fdivmpt.mm"
include "syl.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem refdivmptf
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( F : A --> RR /\ G : A --> RR /\ A e. V ) -> ( F /_f G ) : ( G supp 0 ) --> RR )

  proof
    cA
    cr
    cF
    wf
    #
    cA
    cr
    cG
    wf
    #
    cA
    cV
    wcel
    #
    w3a
    #
    cG
    cc0
    csupp
    co
    #
    cr
    cF
    cG
    cfdiv
    co
    #
    wf
    @4
    cr
    vx
    @4
    vx
    cv
    #
    cF
    cfv
    #
    @6
    cG
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    wf
    @3
    vx
    @4
    @9
    cr
    @10
    @3
    @6
    @4
    wcel
    #
    wa
    #
    @7
    @8
    @12
    cA
    cr
    @6
    cF
    @0
    @1
    @2
    @11
    simpl1
    @3
    @4
    cA
    @6
    @1
    @0
    @4
    cA
    wss
    @2
    @1
    cG
    cdm
    @4
    cA
    cG
    cc0
    suppssdm
    cA
    cr
    cG
    fdm
    syl5sseq
    3ad2ant2
    sselda
    #
    ffvelrnd
    @12
    cA
    cr
    @6
    cG
    @0
    @1
    @2
    @11
    simpl2
    @13
    ffvelrnd
    @3
    @11
    @6
    cA
    wcel
    #
    @8
    cc0
    wne
    #
    @3
    cG
    cA
    wfn
    #
    @2
    cc0
    cr
    wcel
    @11
    @14
    @15
    wa
    wb
    @1
    @0
    @16
    @2
    cA
    cr
    cG
    ffn
    3ad2ant2
    @0
    @1
    @2
    simp3
    @3
    0red
    @6
    cG
    cV
    cr
    cA
    cc0
    elsuppfn
    syl3anc
    simplbda
    redivcld
    @10
    eqid
    fmptd
    @3
    @4
    cr
    @5
    @10
    @3
    cA
    cc
    cF
    wf
    #
    cA
    cc
    cG
    wf
    #
    @2
    w3a
    @5
    @10
    wceq
    @0
    @17
    @1
    @18
    @2
    @2
    @0
    cA
    cr
    cc
    cF
    @0
    id
    cr
    cc
    wss
    #
    @0
    ax-resscn
    a1i
    fssd
    @1
    cA
    cr
    cc
    cG
    @1
    id
    @19
    @1
    ax-resscn
    a1i
    fssd
    @2
    id
    3anim123i
    vx
    cA
    cF
    cG
    cV
    fdivmpt
    syl
    feq1d
    mpbird
end
