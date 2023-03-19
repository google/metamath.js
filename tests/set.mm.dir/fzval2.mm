include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cicc.mm"
include "cin.mm"
include "fzval.mm"
include "cxr.mm"
include "wceq.mm"
include "cr.mm"
include "zssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "sseli.mm"
include "iccval.mm"
include "syl2an.mm"
include "ineq1d.mm"
include "inrab2.mm"
include "wss.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "rabeq.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "syl6req.mm"
include "eqtrd.mm"

theorem fzval2
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M ... N ) = ( ( M [,] N ) i^i ZZ ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cN
    cfz
    co
    cM
    vk
    cv
    #
    cle
    wbr
    @3
    cN
    cle
    wbr
    wa
    #
    vk
    cz
    crab
    #
    cM
    cN
    cicc
    co
    #
    cz
    cin
    #
    vk
    cM
    cN
    fzval
    @2
    @7
    @4
    vk
    cxr
    crab
    #
    cz
    cin
    #
    @5
    @2
    @6
    @8
    cz
    @0
    cM
    cxr
    wcel
    cN
    cxr
    wcel
    @6
    @8
    wceq
    @1
    cz
    cxr
    cM
    cz
    cr
    cxr
    zssre
    ressxr
    sstri
    #
    sseli
    cz
    cxr
    cN
    @10
    sseli
    vk
    cM
    cN
    iccval
    syl2an
    ineq1d
    @9
    @4
    vk
    cxr
    cz
    cin
    #
    crab
    #
    @5
    @4
    vk
    cxr
    cz
    inrab2
    @11
    cz
    wceq
    #
    @12
    @5
    wceq
    cz
    cxr
    wss
    @13
    @10
    cz
    cxr
    sseqin2
    mpbi
    @4
    vk
    @11
    cz
    rabeq
    ax-mp
    eqtri
    syl6req
    eqtrd
end
