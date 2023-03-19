include "cv.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cres.mm"
include "crest.mm"
include "co.mm"
include "chmeo.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "cvmscbv.mm"
include "cvmfolem.mm"

theorem cvmfo
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let cG: class G
  let cP: class P
  assume cvmlift.1: |- B = U. C
  assume cvmfo.2: |- X = U. J


  assert |- ( F e. ( C CovMap J ) -> F : B -onto-> X )

  proof
    vd
    vc
    cB
    cC
    vk
    cJ
    vs
    cv
    #
    cuni
    cF
    ccnv
    vk
    cv
    #
    cima
    wceq
    vu
    cv
    #
    vv
    cv
    cin
    c0
    wceq
    vv
    @0
    @2
    csn
    cdif
    wral
    cF
    @2
    cres
    cC
    @2
    crest
    co
    cJ
    @1
    crest
    co
    chmeo
    co
    wcel
    wa
    vu
    @0
    wral
    wa
    vs
    cC
    cpw
    c0
    csn
    cdif
    crab
    cmpt
    #
    va
    cF
    cJ
    cX
    vb
    vv
    vu
    cC
    @3
    vk
    cF
    cJ
    vs
    va
    vb
    vc
    vd
    @3
    eqid
    cvmscbv
    cvmlift.1
    cvmfo.2
    cvmfolem
end
