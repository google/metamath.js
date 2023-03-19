include "wcel.mm"
include "cn0.mm"
include "wf.mm"
include "c1o.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cmap.mm"
include "co.mm"
include "psr1basf.mm"
include "wf1o.mm"
include "c0.mm"
include "df1o2.mm"
include "nn0ex.mm"
include "0ex.mm"
include "eqid.mm"
include "mapsnf1o3.mm"
include "f1of.mm"
include "ax-mp.mm"
include "fco.mm"
include "sylancl.mm"
include "coe1fval3.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem coe1f2
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cK: class K
  let vx: setvar x
  let vf: setvar f
  let vn: setvar n
  assume coe1fval.a: |- A = ( coe1 ` F )
  assume coe1f2.b: |- B = ( Base ` P )
  assume coe1f2.p: |- P = ( PwSer1 ` R )
  assume coe1f2.k: |- K = ( Base ` R )


  assert |- ( F e. B -> A : NN0 --> K )

  proof
    cF
    cB
    wcel
    #
    cn0
    cK
    cA
    wf
    cn0
    cK
    cF
    vx
    cn0
    c1o
    vx
    cv
    csn
    cxp
    cmpt
    #
    ccom
    #
    wf
    #
    @0
    cn0
    c1o
    cmap
    co
    #
    cK
    cF
    wf
    cn0
    @4
    @1
    wf
    #
    @3
    cB
    cP
    cR
    cF
    cK
    coe1f2.p
    coe1f2.b
    coe1f2.k
    psr1basf
    cn0
    @4
    @1
    wf1o
    @5
    vx
    cn0
    c1o
    @1
    c0
    df1o2
    nn0ex
    0ex
    @1
    eqid
    #
    mapsnf1o3
    cn0
    @4
    @1
    f1of
    ax-mp
    cn0
    @4
    cK
    cF
    @1
    fco
    sylancl
    @0
    cn0
    cK
    cA
    @2
    vx
    cA
    cB
    cP
    cR
    cF
    @1
    coe1fval.a
    coe1f2.b
    coe1f2.p
    @6
    coe1fval3
    feq1d
    mpbird
end
