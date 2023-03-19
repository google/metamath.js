include "csmblfn.mm"
include "cfv.mm"
include "wcel.mm"
include "cmbf.mm"
include "wn.mm"
include "cc0.mm"
include "nfv.mm"
include "csalg.mm"
include "cvol.mm"
include "cdm.mm"
include "dmvolsal.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cr.mm"
include "cuni.mm"
include "unieqi.mm"
include "unidmvol.mm"
include "eqtri.mm"
include "syl6sseqr.mm"
include "0red.mm"
include "smfconst.mm"
include "cv.mm"
include "wa.mm"
include "fmptd.mm"
include "fdmd.mm"
include "wceq.mm"
include "eqcomi.mm"
include "eleq12d.mm"
include "notbid.mm"
include "mpbird.mm"
include "mbfdm.mm"
include "con3i.mm"
include "syl.mm"
include "jca.mm"

theorem smfmbfcex
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cF: class F
  let cX: class X
  let vk: setvar k
  assume smfmbfcex.s: |- S = dom vol
  assume smfmbfcex.x: |- ( ph -> X C_ RR )
  assume smfmbfcex.n: |- ( ph -> -. X e. S )
  assume smfmbfcex.f: |- F = ( x e. X |-> 0 )

  disjoint X x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( F e. ( SMblFn ` S ) /\ -. F e. MblFn ) )

  proof
    wph
    cF
    cS
    csmblfn
    cfv
    wcel
    cF
    cmbf
    wcel
    #
    wn
    #
    wph
    vx
    cX
    cc0
    cS
    cF
    wph
    vx
    nfv
    cS
    csalg
    wcel
    wph
    cS
    cvol
    cdm
    #
    csalg
    smfmbfcex.s
    dmvolsal
    eqeltri
    a1i
    wph
    cX
    cr
    cS
    cuni
    #
    smfmbfcex.x
    @3
    @2
    cuni
    cr
    cS
    @2
    smfmbfcex.s
    unieqi
    unidmvol
    eqtri
    syl6sseqr
    wph
    0red
    smfmbfcex.f
    smfconst
    wph
    cF
    cdm
    #
    @2
    wcel
    #
    wn
    #
    @1
    wph
    @6
    cX
    cS
    wcel
    #
    wn
    smfmbfcex.n
    wph
    @5
    @7
    wph
    @4
    cX
    @2
    cS
    wph
    cX
    cr
    cF
    wph
    vx
    cX
    cc0
    cr
    cF
    wph
    vx
    cv
    cX
    wcel
    wa
    0red
    smfmbfcex.f
    fmptd
    fdmd
    @2
    cS
    wceq
    wph
    cS
    @2
    smfmbfcex.s
    eqcomi
    a1i
    eleq12d
    notbid
    mpbird
    @0
    @5
    cF
    mbfdm
    con3i
    syl
    jca
end
