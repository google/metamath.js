include "cioc.mm"
include "co.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "caddc.mm"
include "cioo.mm"
include "ciin.mm"
include "iooiinioc.mm"
include "eqcomd.mm"
include "wcel.mm"
include "wtru.mm"
include "csalg.mm"
include "bor1sal.mm"
include "a1i.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "nnct.mm"
include "c0.mm"
include "wne.mm"
include "nnn0.mm"
include "wa.mm"
include "iooborel.mm"
include "saliincl.mm"
include "trud.mm"
include "eqeltrd.mm"

theorem iocborel
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x
  assume iocborel.a: |- ( ph -> A e. RR* )
  assume iocborel.c: |- ( ph -> C e. RR )
  assume iocborel.t: |- J = ( topGen ` ran (,) )
  assume iocborel.b: |- B = ( SalGen ` J )


  assert |- ( ph -> ( A (,] C ) e. B )

  proof
    wph
    cA
    cC
    cioc
    co
    #
    vn
    cn
    cA
    cC
    c1
    vn
    cv
    #
    cdiv
    co
    caddc
    co
    #
    cioo
    co
    #
    ciin
    #
    cB
    wph
    @4
    @0
    wph
    cA
    cC
    vn
    iocborel.a
    iocborel.c
    iooiinioc
    eqcomd
    @4
    cB
    wcel
    #
    wph
    @5
    wtru
    cB
    vn
    @3
    cn
    cB
    csalg
    wcel
    wtru
    cB
    cJ
    iocborel.t
    iocborel.b
    bor1sal
    a1i
    cn
    com
    cdom
    wbr
    wtru
    nnct
    a1i
    cn
    c0
    wne
    wtru
    nnn0
    a1i
    @3
    cB
    wcel
    wtru
    @1
    cn
    wcel
    wa
    cA
    cB
    @2
    cJ
    iocborel.t
    iocborel.b
    iooborel
    a1i
    saliincl
    trud
    a1i
    eqeltrd
end
