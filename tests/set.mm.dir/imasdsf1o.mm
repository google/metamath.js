include "c1.mm"
include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "wceq.mm"
include "c2nd.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "w3a.mm"
include "cxp.mm"
include "cmap.mm"
include "crab.mm"
include "cn.mm"
include "cxrs.mm"
include "ccom.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "cxr.mm"
include "cmnf.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "eqid.mm"
include "imasdsf1olem.mm"

theorem imasdsf1o
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vn: setvar n
  let vf: setvar f
  let vj: setvar j
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x
  let cT: class T
  let cS: class S
  let cW: class W
  assume imasdsf1o.u: |- ( ph -> U = ( F "s R ) )
  assume imasdsf1o.v: |- ( ph -> V = ( Base ` R ) )
  assume imasdsf1o.f: |- ( ph -> F : V -1-1-onto-> B )
  assume imasdsf1o.r: |- ( ph -> R e. Z )
  assume imasdsf1o.e: |- E = ( ( dist ` R ) |` ( V X. V ) )
  assume imasdsf1o.d: |- D = ( dist ` U )
  assume imasdsf1o.m: |- ( ph -> E e. ( *Met ` V ) )
  assume imasdsf1o.x: |- ( ph -> X e. V )
  assume imasdsf1o.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( ( F ` X ) D ( F ` Y ) ) = ( X E Y ) )

  proof
    wph
    cB
    cD
    cR
    c1
    vh
    cv
    #
    cfv
    c1st
    cfv
    cF
    cfv
    cX
    cF
    cfv
    wceq
    vn
    cv
    #
    @0
    cfv
    c2nd
    cfv
    cF
    cfv
    cY
    cF
    cfv
    wceq
    vi
    cv
    #
    @0
    cfv
    c2nd
    cfv
    cF
    cfv
    @2
    c1
    caddc
    co
    @0
    cfv
    c1st
    cfv
    cF
    cfv
    wceq
    vi
    c1
    @1
    c1
    cmin
    co
    cfz
    co
    wral
    w3a
    vh
    cV
    cV
    cxp
    c1
    @1
    cfz
    co
    cmap
    co
    crab
    #
    vn
    cn
    vg
    @3
    cxrs
    cE
    vg
    cv
    ccom
    cgsu
    co
    cmpt
    crn
    ciun
    #
    cU
    vg
    vh
    vi
    vn
    cE
    cF
    cV
    cxrs
    cxr
    cmnf
    csn
    cdif
    cress
    co
    #
    cX
    cY
    cZ
    imasdsf1o.u
    imasdsf1o.v
    imasdsf1o.f
    imasdsf1o.r
    imasdsf1o.e
    imasdsf1o.d
    imasdsf1o.m
    imasdsf1o.x
    imasdsf1o.y
    @5
    eqid
    @3
    eqid
    @4
    eqid
    imasdsf1olem
end
