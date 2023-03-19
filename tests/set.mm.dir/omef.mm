include "cpw.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cdm.mm"
include "cuni.mm"
include "wceq.mm"
include "c0.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "come.mm"
include "wcel.mm"
include "wb.mm"
include "isome.mm"
include "syl.mm"
include "mpbid.mm"
include "simplld.mm"
include "simp-4r.mm"
include "pweqi.mm"
include "syl6reqr.mm"
include "feq2d.mm"
include "mpbird.mm"

theorem omef
  let wph: wff ph
  let cO: class O
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  assume omef.o: |- ( ph -> O e. OutMeas )
  assume omef.x: |- X = U. dom O


  assert |- ( ph -> O : ~P X --> ( 0 [,] +oo ) )

  proof
    wph
    cX
    cpw
    #
    cc0
    cpnf
    cicc
    co
    #
    cO
    wf
    cO
    cdm
    #
    @1
    cO
    wf
    #
    wph
    @3
    @2
    @2
    cuni
    #
    cpw
    #
    wceq
    #
    c0
    cO
    cfv
    cc0
    wceq
    #
    wph
    @3
    @6
    wa
    @7
    wa
    #
    vz
    cv
    cO
    cfv
    vy
    cv
    #
    cO
    cfv
    cle
    wbr
    vz
    @9
    cpw
    wral
    vy
    @5
    wral
    #
    @9
    com
    cdom
    wbr
    @9
    cuni
    cO
    cfv
    cO
    @9
    cres
    csumge0
    cfv
    cle
    wbr
    wi
    vy
    @2
    cpw
    wral
    #
    wph
    cO
    come
    wcel
    #
    @8
    @10
    wa
    @11
    wa
    #
    omef.o
    wph
    @12
    @12
    @13
    wb
    omef.o
    vy
    vz
    cO
    come
    isome
    syl
    mpbid
    #
    simplld
    simplld
    wph
    @0
    @2
    @1
    cO
    wph
    @2
    @5
    @0
    wph
    @13
    @6
    @14
    @3
    @6
    @7
    @10
    @11
    simp-4r
    syl
    cX
    @4
    omef.x
    pweqi
    syl6reqr
    feq2d
    mpbird
end
