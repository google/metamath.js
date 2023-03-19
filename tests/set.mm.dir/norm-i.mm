include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wceq.mm"
include "cno.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "normgt0.mm"
include "cr.mm"
include "cle.mm"
include "wb.mm"
include "normcl.mm"
include "normge0.mm"
include "0re.mm"
include "leltne.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "bitrd.mm"
include "necon4bid.mm"
include "bicomd.mm"

theorem norm-i
  let cA: class A


  assert |- ( A e. ~H -> ( ( normh ` A ) = 0 <-> A = 0h ) )

  proof
    cA
    chil
    wcel
    #
    cA
    c0v
    wceq
    cA
    cno
    cfv
    #
    cc0
    wceq
    @0
    cA
    c0v
    @1
    cc0
    @0
    cA
    c0v
    wne
    cc0
    @1
    clt
    wbr
    #
    @1
    cc0
    wne
    #
    cA
    normgt0
    @0
    @1
    cr
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    @2
    @3
    wb
    #
    cA
    normcl
    cA
    normge0
    cc0
    cr
    wcel
    @4
    @5
    @6
    0re
    cc0
    @1
    leltne
    mp3an1
    syl2anc
    bitrd
    necon4bid
    bicomd
end
