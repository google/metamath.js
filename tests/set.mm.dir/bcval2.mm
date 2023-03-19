include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cbc.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "cif.mm"
include "cn0.mm"
include "cz.mm"
include "wceq.mm"
include "elfz3nn0.mm"
include "elfzelz.mm"
include "bcval.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "eqtrd.mm"

theorem bcval2
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vn: setvar n


  assert |- ( K e. ( 0 ... N ) -> ( N _C K ) = ( ( ! ` N ) / ( ( ! ` ( N - K ) ) x. ( ! ` K ) ) ) )

  proof
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cK
    cbc
    co
    #
    @0
    cN
    cfa
    cfv
    cN
    cK
    cmin
    co
    cfa
    cfv
    cK
    cfa
    cfv
    cmul
    co
    cdiv
    co
    #
    cc0
    cif
    #
    @2
    @0
    cN
    cn0
    wcel
    cK
    cz
    wcel
    @1
    @3
    wceq
    cK
    cN
    elfz3nn0
    cK
    cc0
    cN
    elfzelz
    cK
    cN
    bcval
    syl2anc
    @0
    @2
    cc0
    iftrue
    eqtrd
end
