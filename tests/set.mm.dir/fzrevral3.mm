include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "caddc.mm"
include "cv.mm"
include "cmin.mm"
include "wsbc.mm"
include "wb.mm"
include "zaddcl.mm"
include "fzrevral.mm"
include "mpd3an3.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "pncan.mm"
include "pncan2.mm"
include "oveq12d.mm"
include "syl2an.mm"
include "raleqdv.mm"
include "bitrd.mm"

theorem fzrevral3
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vx: setvar x
  let cK: class K

  disjoint j k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint k ph
  disjoint j x
  disjoint K j
  disjoint k x
  disjoint K k
  disjoint K x
  disjoint M x
  disjoint N x
  disjoint ph x
  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( A. j e. ( M ... N ) ph <-> A. k e. ( M ... N ) [. ( ( M + N ) - k ) / j ]. ph ) )

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
    wph
    vj
    cM
    cN
    cfz
    co
    #
    wral
    #
    wph
    vj
    cM
    cN
    caddc
    co
    #
    vk
    cv
    cmin
    co
    wsbc
    #
    vk
    @5
    cN
    cmin
    co
    #
    @5
    cM
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    @6
    vk
    @3
    wral
    @0
    @1
    @5
    cz
    wcel
    @4
    @10
    wb
    cM
    cN
    zaddcl
    wph
    vj
    vk
    @5
    cM
    cN
    fzrevral
    mpd3an3
    @2
    @6
    vk
    @9
    @3
    @0
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @9
    @3
    wceq
    @1
    cM
    zcn
    cN
    zcn
    @11
    @12
    wa
    @7
    cM
    @8
    cN
    cfz
    cM
    cN
    pncan
    cM
    cN
    pncan2
    oveq12d
    syl2an
    raleqdv
    bitrd
end
