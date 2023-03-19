include "chod.mm"
include "co.mm"
include "ch0o.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "chos.mm"
include "honegsubi.mm"
include "eqeq1i.mm"
include "oveq1.mm"
include "sylbir.mm"
include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "neg1cn.mm"
include "homulcl.mm"
include "mp2an.mm"
include "hoadd32i.mm"
include "hoaddassi.mm"
include "hodidi.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "hoaddid1i.mm"
include "ho0f.mm"
include "hoaddcomi.mm"
include "3eqtr3g.mm"
include "syl6eq.mm"
include "impbii.mm"

theorem hosubeq0i
  let cT: class T
  let cU: class U
  assume hosd1.2: |- T : ~H --> ~H
  assume hosd1.3: |- U : ~H --> ~H


  assert |- ( ( T -op U ) = 0hop <-> T = U )

  proof
    cT
    cU
    chod
    co
    #
    ch0o
    wceq
    #
    cT
    cU
    wceq
    #
    @1
    cT
    c1
    cneg
    #
    cU
    chot
    co
    #
    chos
    co
    #
    cU
    chos
    co
    #
    ch0o
    cU
    chos
    co
    #
    cT
    cU
    @1
    @5
    ch0o
    wceq
    @6
    @7
    wceq
    @5
    @0
    ch0o
    cT
    cU
    hosd1.2
    hosd1.3
    honegsubi
    eqeq1i
    @5
    ch0o
    cU
    chos
    oveq1
    sylbir
    @6
    cT
    cU
    chos
    co
    @4
    chos
    co
    #
    cT
    cT
    @4
    cU
    hosd1.2
    @3
    cc
    wcel
    chil
    chil
    cU
    wf
    chil
    chil
    @4
    wf
    neg1cn
    hosd1.3
    @3
    cU
    homulcl
    mp2an
    #
    hosd1.3
    hoadd32i
    @8
    cT
    cU
    @4
    chos
    co
    #
    chos
    co
    #
    cT
    cT
    cU
    @4
    hosd1.2
    hosd1.3
    @9
    hoaddassi
    @11
    cT
    ch0o
    chos
    co
    cT
    @10
    ch0o
    cT
    chos
    @10
    cU
    cU
    chod
    co
    #
    ch0o
    cU
    cU
    hosd1.3
    hosd1.3
    honegsubi
    cU
    hosd1.3
    hodidi
    #
    eqtri
    oveq2i
    cT
    hosd1.2
    hoaddid1i
    eqtri
    eqtri
    eqtri
    @7
    cU
    ch0o
    chos
    co
    cU
    ch0o
    cU
    ho0f
    hosd1.3
    hoaddcomi
    cU
    hosd1.3
    hoaddid1i
    eqtri
    3eqtr3g
    @2
    @0
    @12
    ch0o
    cT
    cU
    cU
    chod
    oveq1
    @13
    syl6eq
    impbii
end
