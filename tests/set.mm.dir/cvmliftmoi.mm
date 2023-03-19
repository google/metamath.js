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
include "cvmliftmolem2.mm"

theorem cvmliftmoi
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cG: class G
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cP: class P
  let cR: class R
  let cT: class T
  let cW: class W
  assume cvmliftmo.b: |- B = U. C
  assume cvmliftmo.y: |- Y = U. K
  assume cvmliftmo.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmliftmo.k: |- ( ph -> K e. Conn )
  assume cvmliftmo.l: |- ( ph -> K e. N-Locally Conn )
  assume cvmliftmo.o: |- ( ph -> O e. Y )
  assume cvmliftmoi.m: |- ( ph -> M e. ( K Cn C ) )
  assume cvmliftmoi.n: |- ( ph -> N e. ( K Cn C ) )
  assume cvmliftmoi.g: |- ( ph -> ( F o. M ) = ( F o. N ) )
  assume cvmliftmoi.p: |- ( ph -> ( M ` O ) = ( N ` O ) )


  assert |- ( ph -> M = N )

  proof
    wph
    vw
    vr
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
    vb
    cF
    cJ
    cK
    cM
    cN
    cO
    cY
    vm
    cvmliftmo.b
    cvmliftmo.y
    cvmliftmo.f
    cvmliftmo.k
    cvmliftmo.l
    cvmliftmo.o
    cvmliftmoi.m
    cvmliftmoi.n
    cvmliftmoi.g
    cvmliftmoi.p
    vv
    vu
    cC
    @3
    vk
    cF
    cJ
    vs
    vb
    vm
    vr
    vw
    @3
    eqid
    cvmscbv
    cvmliftmolem2
end
