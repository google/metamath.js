include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cnt.mm"
include "ioontr.mm"
include "a1i.mm"
include "cr.mm"
include "wss.mm"
include "cn.mm"
include "ioossre.mm"
include "cen.mm"
include "breq1i.mm"
include "biimpi.mm"
include "nnenom.mm"
include "ensymi.mm"
include "domentr.mm"
include "syl2anc.mm"
include "adantl.mm"
include "rectbntr0.mm"
include "eqtr3d.mm"
include "wn.mm"
include "wne.mm"
include "clt.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "ioon0.mm"
include "mpbird.mm"
include "neneqd.mm"
include "adantr.mm"
include "pm2.65da.mm"

theorem ioonct
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ioonct.b: |- ( ph -> A e. RR* )
  assume ioonct.c: |- ( ph -> B e. RR* )
  assume ioonct.l: |- ( ph -> A < B )
  assume ioonct.a: |- C = ( A (,) B )


  assert |- ( ph -> -. C ~<_ _om )

  proof
    wph
    cC
    com
    cdom
    wbr
    #
    cA
    cB
    cioo
    co
    #
    c0
    wceq
    #
    wph
    @0
    wa
    #
    @1
    cioo
    crn
    ctg
    cfv
    cnt
    cfv
    cfv
    #
    @1
    c0
    @4
    @1
    wceq
    @3
    cA
    cB
    ioontr
    a1i
    @3
    @1
    cr
    wss
    #
    @1
    cn
    cdom
    wbr
    #
    @4
    c0
    wceq
    @5
    @3
    cA
    cB
    ioossre
    a1i
    @0
    @6
    wph
    @0
    @1
    com
    cdom
    wbr
    #
    com
    cn
    cen
    wbr
    #
    @6
    @0
    @7
    cC
    @1
    com
    cdom
    ioonct.a
    breq1i
    biimpi
    @8
    @0
    cn
    com
    nnenom
    ensymi
    a1i
    @1
    com
    cn
    domentr
    syl2anc
    adantl
    @1
    rectbntr0
    syl2anc
    eqtr3d
    wph
    @2
    wn
    @0
    wph
    @1
    c0
    wph
    @1
    c0
    wne
    #
    cA
    cB
    clt
    wbr
    #
    ioonct.l
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @9
    @10
    wb
    ioonct.b
    ioonct.c
    cA
    cB
    ioon0
    syl2anc
    mpbird
    neneqd
    adantr
    pm2.65da
end
