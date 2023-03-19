include "c3.mm"
include "c2.mm"
include "clcm.mm"
include "co.mm"
include "cmul.mm"
include "c6.mm"
include "cgcd.mm"
include "c1.mm"
include "wceq.mm"
include "wne.mm"
include "2re.mm"
include "2lt3.mm"
include "gtneii.mm"
include "cprime.mm"
include "wcel.mm"
include "wb.mm"
include "3prm.mm"
include "2prm.mm"
include "prmrp.mm"
include "mp2an.mm"
include "mpbir.mm"
include "oveq2i.mm"
include "cn.mm"
include "3nn.mm"
include "2nn.mm"
include "lcmgcdnn.mm"
include "cz.mm"
include "cn0.mm"
include "nnzi.mm"
include "lcmcl.mm"
include "nn0cni.mm"
include "mulid1i.mm"
include "3eqtr3ri.mm"
include "3t2e6.mm"
include "eqtri.mm"

theorem 3lcm2e6



  assert |- ( 3 lcm 2 ) = 6

  proof
    c3
    c2
    clcm
    co
    #
    c3
    c2
    cmul
    co
    #
    c6
    @0
    c3
    c2
    cgcd
    co
    #
    cmul
    co
    #
    @0
    c1
    cmul
    co
    @1
    @0
    @2
    c1
    @0
    cmul
    @2
    c1
    wceq
    #
    c3
    c2
    wne
    #
    c2
    c3
    2re
    2lt3
    gtneii
    c3
    cprime
    wcel
    c2
    cprime
    wcel
    @4
    @5
    wb
    3prm
    2prm
    c3
    c2
    prmrp
    mp2an
    mpbir
    oveq2i
    c3
    cn
    wcel
    c2
    cn
    wcel
    @3
    @1
    wceq
    3nn
    2nn
    c3
    c2
    lcmgcdnn
    mp2an
    @0
    @0
    c3
    cz
    wcel
    c2
    cz
    wcel
    @0
    cn0
    wcel
    c3
    3nn
    nnzi
    c2
    2nn
    nnzi
    c3
    c2
    lcmcl
    mp2an
    nn0cni
    mulid1i
    3eqtr3ri
    3t2e6
    eqtri
end
