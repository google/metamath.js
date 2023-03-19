include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cfz.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wn.mm"
include "cuz.mm"
include "cfv.mm"
include "fzn0.mm"
include "eluz.mm"
include "syl5bb.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "lenlt.mm"
include "syl2an.mm"
include "bitr2d.mm"
include "necon4bbid.mm"

theorem fzn
  let cM: class M
  let cN: class N
  let cK: class K
  let vk: setvar k
  let vm: setvar m


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( N < M <-> ( M ... N ) = (/) ) )

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
    cN
    cM
    clt
    wbr
    #
    cM
    cN
    cfz
    co
    #
    c0
    @2
    @4
    c0
    wne
    #
    cM
    cN
    cle
    wbr
    #
    @3
    wn
    #
    @5
    cN
    cM
    cuz
    cfv
    wcel
    @2
    @6
    cM
    cN
    fzn0
    cM
    cN
    eluz
    syl5bb
    @0
    cM
    cr
    wcel
    cN
    cr
    wcel
    @6
    @7
    wb
    @1
    cM
    zre
    cN
    zre
    cM
    cN
    lenlt
    syl2an
    bitr2d
    necon4bbid
end
