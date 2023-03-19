include "mrissd.mm"
include "sstrd.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wral.mm"
include "ismri2d.mm"
include "mpbid.mm"
include "sseld.mm"
include "ssdifd.mm"
include "ssdifssd.mm"
include "mrcssd.mm"
include "ssneld.mm"
include "imim12d.mm"
include "ralimdv2.mm"
include "mpd.mm"
include "ismri2dd.mm"

theorem mrissmrid
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cI: class I
  let cN: class N
  let cX: class X
  let vx: setvar x
  assume mrissmrid.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mrissmrid.2: |- N = ( mrCls ` A )
  assume mrissmrid.3: |- I = ( mrInd ` A )
  assume mrissmrid.4: |- ( ph -> S e. I )
  assume mrissmrid.5: |- ( ph -> T C_ S )


  assert |- ( ph -> T e. I )

  proof
    wph
    vx
    cA
    cT
    cI
    cN
    cX
    mrissmrid.2
    mrissmrid.3
    mrissmrid.1
    wph
    cT
    cS
    cX
    mrissmrid.5
    wph
    cA
    cS
    cI
    cX
    mrissmrid.3
    mrissmrid.1
    mrissmrid.4
    mrissd
    #
    sstrd
    wph
    vx
    cv
    #
    cS
    @1
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    wn
    #
    vx
    cS
    wral
    #
    @1
    cT
    @2
    cdif
    #
    cN
    cfv
    #
    wcel
    wn
    #
    vx
    cT
    wral
    wph
    cS
    cI
    wcel
    @6
    mrissmrid.4
    wph
    vx
    cA
    cS
    cI
    cN
    cX
    mrissmrid.2
    mrissmrid.3
    mrissmrid.1
    @0
    ismri2d
    mpbid
    wph
    @5
    @9
    vx
    cS
    cT
    wph
    @1
    cT
    wcel
    @1
    cS
    wcel
    @5
    @9
    wph
    cT
    cS
    @1
    mrissmrid.5
    sseld
    wph
    @8
    @4
    @1
    wph
    cA
    @7
    cN
    @3
    cX
    mrissmrid.1
    mrissmrid.2
    wph
    cT
    cS
    @2
    mrissmrid.5
    ssdifd
    wph
    cS
    cX
    @2
    @0
    ssdifssd
    mrcssd
    ssneld
    imim12d
    ralimdv2
    mpd
    ismri2dd
end
