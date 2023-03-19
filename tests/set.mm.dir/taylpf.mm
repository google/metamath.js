include "cc.mm"
include "wf.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "fzfid.mm"
include "taylplem2.mm"
include "fsumcl.mm"
include "eqid.mm"
include "fmptd.mm"
include "taylpfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem taylpf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cN: class N
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cX: class X
  assume taylpfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylpfval.f: |- ( ph -> F : A --> CC )
  assume taylpfval.a: |- ( ph -> A C_ S )
  assume taylpfval.n: |- ( ph -> N e. NN0 )
  assume taylpfval.b: |- ( ph -> B e. dom ( ( S Dn F ) ` N ) )
  assume taylpfval.t: |- T = ( N ( S Tayl F ) B )


  assert |- ( ph -> T : CC --> CC )

  proof
    wph
    cc
    cc
    cT
    wf
    cc
    cc
    vx
    cc
    cc0
    cN
    cfz
    co
    #
    cB
    vk
    cv
    #
    cS
    cF
    cdvn
    co
    cfv
    cfv
    @1
    cfa
    cfv
    cdiv
    co
    vx
    cv
    #
    cB
    cmin
    co
    @1
    cexp
    co
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    wf
    wph
    vx
    cc
    @4
    cc
    @5
    wph
    @2
    cc
    wcel
    wa
    #
    @0
    @3
    vk
    @6
    cc0
    cN
    fzfid
    wph
    cA
    cB
    cS
    vk
    cF
    cN
    @2
    taylpfval.s
    taylpfval.f
    taylpfval.a
    taylpfval.n
    taylpfval.b
    taylplem2
    fsumcl
    @5
    eqid
    fmptd
    wph
    cc
    cc
    cT
    @5
    wph
    vx
    cA
    cB
    cS
    cT
    vk
    cF
    cN
    taylpfval.s
    taylpfval.f
    taylpfval.a
    taylpfval.n
    taylpfval.b
    taylpfval.t
    taylpfval
    feq1d
    mpbird
end
