include "cun.mm"
include "cpw.mm"
include "wcel.mm"
include "cvv.mm"
include "cdif.mm"
include "elex.mm"
include "wb.mm"
include "difex2.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "wss.mm"
include "elpwg.mm"
include "difexg.mm"
include "syl.mm"
include "uncom.mm"
include "sseq2i.mm"
include "ssundif.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "pm5.21nii.mm"

theorem elpwun
  let cA: class A
  let cB: class B
  let cC: class C
  assume eldifpw.1: |- C e. _V


  assert |- ( A e. ~P ( B u. C ) <-> ( A \ C ) e. ~P B )

  proof
    cA
    cB
    cC
    cun
    #
    cpw
    #
    wcel
    #
    cA
    cvv
    wcel
    #
    cA
    cC
    cdif
    #
    cB
    cpw
    #
    wcel
    #
    cA
    @1
    elex
    @6
    @4
    cvv
    wcel
    #
    @3
    @4
    @5
    elex
    cC
    cvv
    wcel
    @3
    @7
    wb
    eldifpw.1
    cA
    cC
    cvv
    difex2
    ax-mp
    sylibr
    @3
    @2
    cA
    @0
    wss
    #
    @6
    cA
    @0
    cvv
    elpwg
    @3
    @6
    @4
    cB
    wss
    #
    @8
    @3
    @7
    @6
    @9
    wb
    cA
    cC
    cvv
    difexg
    @4
    cB
    cvv
    elpwg
    syl
    @8
    cA
    cC
    cB
    cun
    #
    wss
    @9
    @0
    @10
    cA
    cB
    cC
    uncom
    sseq2i
    cA
    cC
    cB
    ssundif
    bitri
    syl6rbbr
    bitrd
    pm5.21nii
end
