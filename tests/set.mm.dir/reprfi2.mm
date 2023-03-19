include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "cin.mm"
include "cfn.mm"
include "reprinfz1.mm"
include "cn.mm"
include "wss.mm"
include "inss2.mm"
include "fz1ssnn.mm"
include "sstri.mm"
include "a1i.mm"
include "nn0zd.mm"
include "wcel.mm"
include "fzfi.mm"
include "ssfid.mm"
include "reprfi.mm"
include "eqeltrd.mm"

theorem reprfi2
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume reprinfz1.n: |- ( ph -> N e. NN0 )
  assume reprinfz1.s: |- ( ph -> S e. NN0 )
  assume reprinfz1.a: |- ( ph -> A C_ NN )


  assert |- ( ph -> ( A ( repr ` S ) N ) e. Fin )

  proof
    wph
    cA
    cN
    cS
    crepr
    cfv
    #
    co
    cA
    c1
    cN
    cfz
    co
    #
    cin
    #
    cN
    @0
    co
    cfn
    wph
    cA
    cS
    cN
    reprinfz1.n
    reprinfz1.s
    reprinfz1.a
    reprinfz1
    wph
    @2
    cS
    cN
    @2
    cn
    wss
    wph
    @2
    @1
    cn
    cA
    @1
    inss2
    #
    cN
    fz1ssnn
    sstri
    a1i
    wph
    cN
    reprinfz1.n
    nn0zd
    reprinfz1.s
    wph
    @1
    @2
    @1
    cfn
    wcel
    wph
    c1
    cN
    fzfi
    a1i
    @2
    @1
    wss
    wph
    @3
    a1i
    ssfid
    reprfi
    eqeltrd
end
