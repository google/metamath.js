include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cpl1.mm"
include "cfv.mm"
include "cascl.mm"
include "cmpt2.mm"
include "cvv.mm"
include "simpl.mm"
include "jca.mm"
include "adantr.mm"
include "mpt2exga.mm"
include "syl.mm"
include "eqid.mm"
include "mat2pmatfval.mm"
include "m2cpm.mm"
include "3expa.mm"
include "fmpt2d.mm"

theorem m2cpmf
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let vb: setvar b
  let vm: setvar m
  assume m2cpm.s: |- S = ( N ConstPolyMat R )
  assume m2cpm.t: |- T = ( N matToPolyMat R )
  assume m2cpm.a: |- A = ( N Mat R )
  assume m2cpm.b: |- B = ( Base ` A )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T : B --> S )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    vm
    vb
    cB
    vi
    vj
    cN
    cN
    vi
    cv
    vj
    cv
    vm
    cv
    #
    co
    cR
    cpl1
    cfv
    #
    cascl
    cfv
    #
    cfv
    #
    cmpt2
    #
    cS
    cT
    cvv
    @2
    @3
    cB
    wcel
    #
    wa
    @0
    @0
    wa
    #
    @7
    cvv
    wcel
    @2
    @9
    @8
    @2
    @0
    @0
    @0
    @1
    simpl
    #
    @10
    jca
    adantr
    vi
    vj
    cN
    cN
    @6
    cfn
    cfn
    mpt2exga
    syl
    vi
    vj
    cA
    cB
    @4
    cR
    @5
    cT
    vm
    cN
    crg
    m2cpm.t
    m2cpm.a
    m2cpm.b
    @4
    eqid
    @5
    eqid
    mat2pmatfval
    @0
    @1
    vb
    cv
    #
    cB
    wcel
    @11
    cT
    cfv
    cS
    wcel
    cA
    cB
    cR
    cS
    cT
    @11
    cN
    m2cpm.s
    m2cpm.t
    m2cpm.a
    m2cpm.b
    m2cpm
    3expa
    fmpt2d
end
