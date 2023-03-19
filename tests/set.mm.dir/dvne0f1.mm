include "cicc.mm"
include "co.mm"
include "crn.mm"
include "wf1.mm"
include "cr.mm"
include "wss.mm"
include "clt.mm"
include "wiso.mm"
include "ccnv.mm"
include "wo.mm"
include "wf1o.mm"
include "dvne0.mm"
include "isof1o.mm"
include "jaoi.mm"
include "f1of1.mm"
include "3syl.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cncff.mm"
include "frn.mm"
include "f1ss.mm"
include "syl2anc.mm"

theorem dvne0f1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dvne0.a: |- ( ph -> A e. RR )
  assume dvne0.b: |- ( ph -> B e. RR )
  assume dvne0.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )
  assume dvne0.d: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume dvne0.z: |- ( ph -> -. 0 e. ran ( RR _D F ) )


  assert |- ( ph -> F : ( A [,] B ) -1-1-> RR )

  proof
    wph
    cA
    cB
    cicc
    co
    #
    cF
    crn
    #
    cF
    wf1
    #
    @1
    cr
    wss
    #
    @0
    cr
    cF
    wf1
    wph
    @0
    @1
    clt
    clt
    cF
    wiso
    #
    @0
    @1
    clt
    clt
    ccnv
    #
    cF
    wiso
    #
    wo
    @0
    @1
    cF
    wf1o
    #
    @2
    wph
    cA
    cB
    cF
    dvne0.a
    dvne0.b
    dvne0.f
    dvne0.d
    dvne0.z
    dvne0
    @4
    @7
    @6
    @0
    @1
    clt
    clt
    cF
    isof1o
    @0
    @1
    clt
    @5
    cF
    isof1o
    jaoi
    @0
    @1
    cF
    f1of1
    3syl
    wph
    cF
    @0
    cr
    ccncf
    co
    wcel
    @0
    cr
    cF
    wf
    @3
    dvne0.f
    @0
    cr
    cF
    cncff
    @0
    cr
    cF
    frn
    3syl
    @0
    @1
    cr
    cF
    f1ss
    syl2anc
end
