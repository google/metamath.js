include "cv.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cxr.mm"
include "adantr.mm"
include "cc0.mm"
include "cfz.mm"
include "wf.mm"
include "cfzo.mm"
include "simpr.mm"
include "fourierdlem1.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"

theorem fourierdlem8
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cI: class I
  let cM: class M
  let vx: setvar x
  let vk: setvar k
  assume fourierdlem8.a: |- ( ph -> A e. RR* )
  assume fourierdlem8.b: |- ( ph -> B e. RR* )
  assume fourierdlem8.q: |- ( ph -> Q : ( 0 ... M ) --> ( A [,] B ) )
  assume fourierdlem8.i: |- ( ph -> I e. ( 0 ..^ M ) )


  assert |- ( ph -> ( ( Q ` I ) [,] ( Q ` ( I + 1 ) ) ) C_ ( A [,] B ) )

  proof
    wph
    vx
    cv
    #
    cA
    cB
    cicc
    co
    #
    wcel
    #
    vx
    cI
    cQ
    cfv
    cI
    c1
    caddc
    co
    cQ
    cfv
    cicc
    co
    #
    wral
    @3
    @1
    wss
    wph
    @2
    vx
    @3
    wph
    @0
    @3
    wcel
    #
    wa
    cA
    cB
    cQ
    cI
    cM
    @0
    wph
    cA
    cxr
    wcel
    @4
    fourierdlem8.a
    adantr
    wph
    cB
    cxr
    wcel
    @4
    fourierdlem8.b
    adantr
    wph
    cc0
    cM
    cfz
    co
    @1
    cQ
    wf
    @4
    fourierdlem8.q
    adantr
    wph
    cI
    cc0
    cM
    cfzo
    co
    wcel
    @4
    fourierdlem8.i
    adantr
    wph
    @4
    simpr
    fourierdlem1
    ralrimiva
    vx
    @3
    @1
    dfss3
    sylibr
end
