include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cc.mm"
include "cmpt.mm"
include "eqid.mm"
include "wss.mm"
include "wcel.mm"
include "ccncf.mm"
include "addccncf2.mm"
include "syl2anc.mm"
include "ssid.mm"
include "a1i.mm"
include "cncfmptssg.mm"
include "cncfcompt.mm"

theorem fourierdlem23
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem23.a: |- ( ph -> A C_ CC )
  assume fourierdlem23.f: |- ( ph -> F e. ( A -cn-> CC ) )
  assume fourierdlem23.b: |- ( ph -> B C_ CC )
  assume fourierdlem23.x: |- ( ph -> X e. CC )
  assume fourierdlem23.xps: |- ( ( ph /\ s e. B ) -> ( X + s ) e. A )

  disjoint A s
  disjoint B s
  disjoint F s
  disjoint X s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> ( s e. B |-> ( F ` ( X + s ) ) ) e. ( B -cn-> CC ) )

  proof
    wph
    vs
    cB
    cX
    vs
    cv
    caddc
    co
    #
    cA
    cc
    cF
    wph
    vs
    cB
    cc
    cB
    cA
    @0
    vs
    cB
    @0
    cmpt
    #
    @1
    eqid
    #
    wph
    cB
    cc
    wss
    cX
    cc
    wcel
    @1
    cB
    cc
    ccncf
    co
    wcel
    fourierdlem23.b
    fourierdlem23.x
    vs
    cB
    cX
    @1
    @2
    addccncf2
    syl2anc
    cB
    cB
    wss
    wph
    cB
    ssid
    a1i
    fourierdlem23.a
    fourierdlem23.xps
    cncfmptssg
    fourierdlem23.f
    cncfcompt
end
