include "cv.mm"
include "crn.mm"
include "cres.mm"
include "wf1o.mm"
include "cpw.mm"
include "wrex.mm"
include "csumge0.mm"
include "cfv.mm"
include "ccom.mm"
include "cle.mm"
include "wbr.mm"
include "ffnd.mm"
include "wessf1orn.mm"
include "wcel.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "simp2.mm"
include "simp3.mm"
include "sge0resrnlem.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem sge0resrn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vk: setvar k
  assume sge0resrn.a: |- ( ph -> A e. V )
  assume sge0resrn.f: |- ( ph -> F : B --> ( 0 [,] +oo ) )
  assume sge0resrn.g: |- ( ph -> G : A --> B )
  assume sge0resrn.r: |- ( ph -> R We A )


  assert |- ( ph -> ( sum^ ` ( F |` ran G ) ) <_ ( sum^ ` ( F o. G ) ) )

  proof
    wph
    vx
    cv
    #
    cG
    crn
    #
    cG
    @0
    cres
    wf1o
    #
    vx
    cA
    cpw
    #
    wrex
    cF
    @1
    cres
    csumge0
    cfv
    cF
    cG
    ccom
    csumge0
    cfv
    cle
    wbr
    #
    wph
    vx
    cA
    cR
    cG
    cV
    wph
    cA
    cB
    cG
    sge0resrn.g
    ffnd
    sge0resrn.a
    sge0resrn.r
    wessf1orn
    wph
    @2
    @4
    vx
    @3
    wph
    @0
    @3
    wcel
    #
    @2
    @4
    wph
    @5
    @2
    w3a
    cA
    cB
    cF
    cG
    cV
    @0
    wph
    @5
    cA
    cV
    wcel
    @2
    sge0resrn.a
    3ad2ant1
    wph
    @5
    cB
    cc0
    cpnf
    cicc
    co
    cF
    wf
    @2
    sge0resrn.f
    3ad2ant1
    wph
    @5
    cA
    cB
    cG
    wf
    @2
    sge0resrn.g
    3ad2ant1
    wph
    @5
    @2
    simp2
    wph
    @5
    @2
    simp3
    sge0resrnlem
    3exp
    rexlimdv
    mpd
end
