include "csad.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "wss.mm"
include "sadcl.mm"
include "syl2anc.mm"
include "sseld.mm"
include "unssd.mm"
include "wb.mm"
include "wa.mm"
include "c2o.mm"
include "c0.mm"
include "wcad.mm"
include "c1o.mm"
include "cif.mm"
include "cmpt2.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "cmpt.mm"
include "cseq.mm"
include "adantr.mm"
include "cin.mm"
include "eqid.mm"
include "simpr.mm"
include "saddisjlem.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem saddisj
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cC: class C
  let cN: class N
  assume saddisj.1: |- ( ph -> A C_ NN0 )
  assume saddisj.2: |- ( ph -> B C_ NN0 )
  assume saddisj.3: |- ( ph -> ( A i^i B ) = (/) )


  assert |- ( ph -> ( A sadd B ) = ( A u. B ) )

  proof
    wph
    vk
    cA
    cB
    csad
    co
    #
    cA
    cB
    cun
    #
    wph
    vk
    cv
    #
    cn0
    wcel
    #
    @2
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wph
    @0
    cn0
    @2
    wph
    cA
    cn0
    wss
    #
    cB
    cn0
    wss
    #
    @0
    cn0
    wss
    saddisj.1
    saddisj.2
    cA
    cB
    sadcl
    syl2anc
    sseld
    wph
    @1
    cn0
    @2
    wph
    cA
    cB
    cn0
    saddisj.1
    saddisj.2
    unssd
    sseld
    wph
    @3
    @4
    @5
    wb
    wph
    @3
    wa
    cA
    cB
    vc
    vm
    c2o
    cn0
    vm
    cv
    #
    cA
    wcel
    @8
    cB
    wcel
    c0
    vc
    cv
    wcel
    wcad
    c1o
    c0
    cif
    cmpt2
    vx
    cn0
    vx
    cv
    #
    cc0
    wceq
    c0
    @9
    c1
    cmin
    co
    cif
    cmpt
    cc0
    cseq
    #
    vm
    vx
    @2
    vc
    wph
    @6
    @3
    saddisj.1
    adantr
    wph
    @7
    @3
    saddisj.2
    adantr
    wph
    cA
    cB
    cin
    c0
    wceq
    @3
    saddisj.3
    adantr
    @10
    eqid
    wph
    @3
    simpr
    saddisjlem
    ex
    pm5.21ndd
    eqrdv
end
