include "cfv.mm"
include "mrcssvd.mm"
include "mrcssd.mm"
include "sstrd.mm"
include "mrcidmd.mm"
include "sseqtrd.mm"
include "eqssd.mm"

theorem mressmrcd
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cN: class N
  let cX: class X
  assume mressmrcd.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mressmrcd.2: |- N = ( mrCls ` A )
  assume mressmrcd.3: |- ( ph -> S C_ ( N ` T ) )
  assume mressmrcd.4: |- ( ph -> T C_ S )


  assert |- ( ph -> ( N ` S ) = ( N ` T ) )

  proof
    wph
    cS
    cN
    cfv
    #
    cT
    cN
    cfv
    #
    wph
    @0
    @1
    cN
    cfv
    @1
    wph
    cA
    cS
    cN
    @1
    cX
    mressmrcd.1
    mressmrcd.2
    mressmrcd.3
    wph
    cA
    cT
    cN
    cX
    mressmrcd.1
    mressmrcd.2
    mrcssvd
    #
    mrcssd
    wph
    cA
    cT
    cN
    cX
    mressmrcd.1
    mressmrcd.2
    wph
    cT
    cS
    cX
    mressmrcd.4
    wph
    cS
    @1
    cX
    mressmrcd.3
    @2
    sstrd
    #
    sstrd
    mrcidmd
    sseqtrd
    wph
    cA
    cT
    cN
    cS
    cX
    mressmrcd.1
    mressmrcd.2
    mressmrcd.4
    @3
    mrcssd
    eqssd
end
