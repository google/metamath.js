include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "elfzelz.mm"
include "ax-mp.mm"
include "elfzle1.mm"
include "caddc.mm"
include "cr.mm"
include "zrei.mm"
include "nnrei.mm"
include "elfzle2.mm"
include "letrp1.mm"
include "mp3an.mm"
include "breqtrri.mm"
include "w3a.mm"
include "wb.mm"
include "1z.mm"
include "cn.mm"
include "nnz.mm"
include "peano2z.mm"
include "mp2b.mm"
include "eqeltri.mm"
include "elfz1.mm"
include "mp2an.mm"
include "mpbir3an.mm"

theorem jm2.27dlem2
  let cA: class A
  let cB: class B
  let cC: class C
  assume jm2.27dlem2.1: |- A e. ( 1 ... B )
  assume jm2.27dlem2.2: |- C = ( B + 1 )
  assume jm2.27dlem2.3: |- B e. NN


  assert |- A e. ( 1 ... C )

  proof
    cA
    c1
    cC
    cfz
    co
    wcel
    #
    cA
    cz
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    cA
    cC
    cle
    wbr
    #
    cA
    c1
    cB
    cfz
    co
    wcel
    #
    @1
    jm2.27dlem2.1
    cA
    c1
    cB
    elfzelz
    ax-mp
    #
    @4
    @2
    jm2.27dlem2.1
    cA
    c1
    cB
    elfzle1
    ax-mp
    cA
    cB
    c1
    caddc
    co
    #
    cC
    cle
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cle
    wbr
    #
    cA
    @6
    cle
    wbr
    cA
    @5
    zrei
    cB
    jm2.27dlem2.3
    nnrei
    @4
    @7
    jm2.27dlem2.1
    cA
    c1
    cB
    elfzle2
    ax-mp
    cA
    cB
    letrp1
    mp3an
    jm2.27dlem2.2
    breqtrri
    c1
    cz
    wcel
    cC
    cz
    wcel
    @0
    @1
    @2
    @3
    w3a
    wb
    1z
    cC
    @6
    cz
    jm2.27dlem2.2
    cB
    cn
    wcel
    cB
    cz
    wcel
    @6
    cz
    wcel
    jm2.27dlem2.3
    cB
    nnz
    cB
    peano2z
    mp2b
    eqeltri
    cA
    c1
    cC
    elfz1
    mp2an
    mpbir3an
end
